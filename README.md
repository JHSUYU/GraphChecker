# GraphChecker

**What this is (the owner's standing statement, 2026-09-23).** A purely academic research
project in software engineering and distributed systems: a PhD study of how open-source
distributed systems (Hadoop HDFS here) fail under configuration, clock and message-delivery
counterfactuals, carried out on recorded runs of the systems' own test workloads. Nothing in
it targets a production deployment; every Hadoop tree it drives is a local MiniDFSCluster
checkout, every finding is an SMT witness over the project's own rows, and the deliverable is
the method and its evaluation on the nine HDFS cases below. Anyone (or any tool) picking this
repository up should read it in that light.

This file is the design, the status and the handover in one place. Read it top to bottom
before changing anything; section 10 is the ordered to-do, section 11 is how to run and
debug a round. The reference designs it derives from are listed in section 13; everything
else that used to live under `docs/` was historical and has been deleted.

## 1. What GraphChecker answers

You have a distributed Java system, a failure that some configuration, clock, message loss
or message ordering can cause, and one recorded run of a workload that does **not** fail.
You annotate the exception construction that is the failure, name the occurrence of it the
case is about, and declare a handful of inputs: which cells are roots (configured sources,
clock reads), which message fields cross which boundary (and therefore which transports may
fail), and a bound for each retained loop. GraphChecker then explores single counterfactual
decisions around that run — a root moved, a clock skewed, a message that fails to leave —
and publishes: `candidate.smt2`, a quantifier-free SMT query whose satisfying valuation *is*
the condition under which the annotated site fails; `claim.json`, stating the finding kind,
which declared roots the witness had to move, and whether the polarity decides (the same
formula refutes the run as it happened); and `confirm.json`, one replay of the witness's
world with no decision forced, which must reach the anchor and observe the fatal. Anything
the recording does not state is refused by name rather than defaulted.

## 2. The core idea

Seven commitments; the rest of the system is derivable from them.

**Roots are declared, not discovered.** A symbol enters at exactly three kinds of place, all
named by the case: a *root* mint (a fault marker at a transport door, a configured source, a
clock read), a *declared region input* (a read of a cell the case names, minting a placeholder
for the value read), and a *wire attach* (an inbound leaf, minting a handoff `v_H` paired with
the producer's export). Everything else stays concrete until a symbolic value is *written*
into it.

**Values propagate inside the JVM; the static graph only scopes.** Replays run on a customized
OpenJDK 8 Zero interpreter that keeps a shadow expression under each value — by value, under
the real object identity — so a read returns the expression written there, through fields,
containers, threads and across the wire. The static slice decides only which regions are
instrumented and which write and export sites of a demanded location are observed. It never
finds a writer, reconstructs provenance, or stitches an input to an output. The Java-side view
of that VM is [docs/CONCOLIC_INTEGRATION.md](docs/CONCOLIC_INTEGRATION.md).

**One structural identity, computed the same way in both passes.** An occurrence is addressed
by where it is in the program and why it ran — never by a thread id, an address or a per-run
counter — and both passes feed that function the same inputs (§4), so sameness is equality.

**The replay unit is one decision flip on one occurrence, in one world.** A focused replay
makes one occurrence symbolic (or one state-connected factor), plants the world it is asked
about (root values, clock skews, answered handoffs, inherited flips) and holds the schedule
prefix of the session it was cut from (§6), then asks that occurrence to take the other arm of
one decision at one site and ordinal. Such a replay *collects an arm the recording lacks*; it
confirms nothing by itself.

**Edges are joined in the SMT, not by execution.** No replay realizes a cross-node chain end
to end. Each publishes its own path condition and expressions; the composer merges them into
one disjunction, and a message or shared-state edge becomes a *family* of arms over the
handoff variable the consumer minted, each arm keyed by the world it was collected in.

**A witness is the world nearest the recording.** Every flip query bounds each root and clock
by its declared window and asks z3 for the model minimizing Σ|x − recorded(x)| (§5); the
published witness is the smallest move that still takes the other arm, and CONFIRM re-runs
exactly the world a replay already ran.

**Fail closed, by name.** Every refusal is a gap row of a closed kind (`contract/GapKind.java`
is the registry), classed `BLOCKING` (the stage fails, naming the row, field and owner) or
`DIAGNOSTIC` (recorded, the campaign goes on). No cap, default, heuristic match or synthesized
value anywhere.

### Why not the simpler designs

*Symbolic propagation alone.* The recording is the healthy run. When a root reaches the target
only through **control dependence** — a store the healthy arm skips — the fatal predicate on the
recorded path is a literal, and no formula over the recording alone is satisfiable at a flipped
root; HDFS-17960 is exactly this shape.

*Linked replay.* Making a primary occurrence and its companions symbolic in one run couples
admission of unrelated regions and grows replays as the *product* of local path counts. Focused
replays cost the *sum*, and the edge is joined afterwards by the family.

*Exhaustive flipping.* HDFS-17960's seed session publishes 1,113 decision rows. Demand starts
at the annotated site and the closure grows only along boundary inputs of demanded values and
the senders of the messages a task served; an obligation is owed once across the corpus
(`explore/Frontier`).

## 3. The pipeline

One campaign per case, driven by `run_engine.sh` (3.8k lines of bash; every stage is a
`campaign_<stage>` function). Inputs are frozen before any work and the iteration writes one
immutable directory, `<out>/schedule/iteration-0000/`, with `final/` beside it.

| Stage | Consumes | Produces | Gate |
| --- | --- | --- | --- |
| `PREFLIGHT`, `FREEZE_TOOL`, `SETUP`, `FREEZE` | workflow config, jar, workload tree | frozen inputs (`frozen-inputs/`, digested) | an unknown config key, or a frozen input changed after freezing, is refused by name |
| `SEED` | workload command, stock JDK 8 | the static slice (`static_scope_map.jsonl`, candidate graph, region skeletons) and **two recording passes**: lite (activation envelopes over every candidate region → `skeleton-pass/region_skeletons.jsonl`) then rich (`concolic_region_plan.jsonl`, `runtime_trace.jsonl`, `recorded_schedule.jsonl`) | recording opens only after the workload registers its node sources; the trace states the window only |
| `PLAN` | both passes, the scope map, the declarations | `execution_task_plan.jsonl`: one row per planned occurrence, the declared target resolved to a full address, the symbolize actions (declared inputs, clocks, `EXPLICIT_SYMBOLIC_FAULT` markers) | two activations sharing one address inside the closure is `OCCURRENCE_ADDRESS_SHARED` BLOCKING; a loop without a declared bound is refused |
| `INSTRUMENT` | selected skeletons, scope map | woven classes (`instrumented-classes/`) | every woven body validated, then JVM-verified fail-closed |
| `REPLAY` (seed) | woven classes, the custom VM | the seed **session**: one file per row kind, `schedule.jsonl`, its expression table | the seed must publish a target row that reached the anchor |
| `IMPORT` | the seed, then every wave's sessions | gap rows | the row contract (§5), checked here and nowhere else |
| `EXPLORE` | every session so far, scope map, root domains | per wave `obligations-NNNN/`: `obligations.jsonl`, one worker dir per obligation (`obligation.jsonl`, `focused_task.jsonl`, `obligation_query.smt2`, `obligation_result.jsonl`), the session it ran, `graph.jsonl`/`growth.jsonl` (§7), and `GROW` when a world exposed a region | a solver error is `NOT_ADMITTED`, never unsat; a flip a session already recorded is not re-asked; nesting is bounded by `region_path_max_world_depth` (3) |
| `COMPOSE` | the corpus, families, root domains | `candidate.smt2`, `candidate_composition_manifest.json` | a read that joins no version and pins no value is `UNSTATED_VALUE`; a replay whose mint and obligation state a root twice and differently is refused |
| `SOLVE`, `DECIDE` | the composed query | a z3 answer per valuation, `claim.json` | satisfiable at the recorded valuation on a healthy recording is a blocking alarm |
| `CONFIRM` | the claim, the manifest, the selected session's obligation | `confirm/` (a focused replay with no flip forced), `final/confirm.json` | anchor reached, fatal observed, no `CONFIRM_MISMATCH` on an expected edge, no `SCHEDULE_DIVERGED` before the cut; otherwise the claim is `SAT_UNCONFIRMED` |
| `EMIT` | all of the above | `result.json`, `gaps.json`, `run-manifest.json` | acceptance is the claim **and** the named gaps **and** the confirmation together |

`EXPLORE` runs in waves: one JVM plans the wave (`explore/ExploreMain`) — reading every session
so far and writing the obligations the frontier is owed — and one worker per obligation runs a
focused replay (`runtime/FocusedReplay`), locally or on a remote host (`campaign_dispatch_wave`,
`schedule_worker_hosts`). The closure it walks (`explore/ClosurePlanner`) starts at the
annotated target — the operands of the fatal predicate and the guard set of the target site —
and grows along the rows (the producer that paired with an attach, the writers whose versions a
read could have observed), the static map (occurrences of regions holding a write or export
site of a demanded location), and **control producers**: the occurrence that sent the message a
task served, whose fault decisions are flip sites. Fault flips are proposed first in the first
wave that reaches an occurrence.

The Java side is organized by those notions:

| Package | Holds |
| --- | --- |
| `contract` | the row kinds, the identity types (`OccurrenceAddress`, `CausalContext`, `ExecutionIndex`, `LocationId`, `Endpoint`), `ScheduleEvent`, `GapKind`/`GapClass`, `ObligationDir`, `SessionReader`, and the `IMPORT` gate (`RowInvariants`) |
| `causynth` | the Soot pass: static slice, weaving and its verification, failure-directed region scoping (`RuntimeSelectedRegionFinalizer`), the wire-flow catalog, the aggregation of both recording passes |
| `plan` | `StaticScopeMap`, `ExecutionTask`, `ConcolicScheduler`, declared inputs (`DeclaredSiteCapture`, `SymbolicInputSelection`), loop-bound policy, `ExposedRegionPlanMain` |
| `runtime` | the recording and replay hooks (`CausynthTraceRecorder`, `ConcolicRegionRuntime`, `RowRuntime`), identity (`Identity`, `Lineage`, `Attribution`, `RecordingWindow`), the schedule (`ScheduleLog`, `TimedWaits`, `WakeScopes`), mints (`RootMint`, `RowPlaceholderMint`, `HandoffMint`), `FocusedReplay`, `Confirmation`, the VM broker |
| `explore` | `Corpus`, `ClosurePlanner`, `Frontier`, `FlipQuery`/`FlipQueryText`, `ObligationFactory`, `SchedulePrefix`, `SlotTable`, `WaveGraph`, `ExploreMain`, `ConfirmMain` |
| `compose` | `Composer`, `ComposedFamilies`, `SmtLowering`/`VmLoweringCore`, the container model (`ContainerSmtCodec`), `ClaimPolicy`, `ComposeMain` |
| `smt` | the expression IR, `Arms` (path conditions, arms, families), canonical JSON, the z3 driver (`Z3`) |
| `annotation` | `@CausynthExceptionTarget`, and `Debug.makeSymbolicBoolean` for a fault marker |
| `src/shim` | `org.apache.hadoop.ipc.CausynthMessagePropagation`, the small jar the Hadoop trees call (message doors, SASL halves, `replaying()`) |

## 4. Identity

An occurrence's address is structural, and it is the same function of the same inputs in the
recording pass and in every replay:

```
OccurrenceAddress = node#epochN            logical component (epoch 1 after a restart)
                  / region/REGION.<id>     static region (code)
                  / ctx:<CausalContext>    why this occurrence ran
                  / idx:<frame>/<frame>/…  where in the component's control structure
```

`CausalContext` has three forms. `Anchor(producerEndpointId, rpcSite)` — a message started it,
and the anchor is the producer's endpoint id, recursively carrying the producer's own context.
`Root(role/api, k)` — a workload action or daemon turn with no incoming message, the k-th such
root of that role and api **in the recording window**. `Lost(role)` — the scope was
unattributable: degraded, and still an identity.

The execution index is PEPID-shaped: the frames from the **scope root** to the region entry,
each a static call site with the iteration count of its innermost enclosing loop. **The one
scope-base rule** (`Identity.scopeStart`): an occurrence's index is relative to its causal
context's own origin — for an `ANCHOR` hop the inbound scope itself, for a `SCOPE_ROOT` the
scope's start, for a `STARTED_ROOT` (a daemon tick) the start frame its work claimed. The
frames above that point belong to the thread that carried the work there and never enter an
address: which pooled IPC handler serves a request is scheduling, not identity. A degraded
(`ROLE.*`) occurrence obeys the same rule; measuring it from the thread's first frame put the
handler's start iteration into every response endpoint and broke 17960 as soon as one heartbeat
shifted the handler rotation.

An **endpoint** — what a message pairing, a read or a write is addressed by — is `(occurrence,
site, site-local execution index, attempt)`; `Endpoint.id()` digests it, and the receiver's
anchor *is* the producer's endpoint id. Site counts (`State.nextSiteEvent`) are keyed by
(level, root hop, site) and start at zero in that calling context.

**Window rules.** Every identity count starts at the window (`Identity.window`,
`Lineage.openWindow`): a frame entered before the window stands at iteration 0 in any in-window
address; a tick or wake turn begun before the window renders k = 0; a request root keeps its k
(the workload may open it pre-window and name it in the declared target). The trace states the
window only — nothing before it opens is written — so pre-window activations never reach PLAN.

**A state location's owner is the VM's own object identity, not an allocation site.**
`KIND/<ownerSymRid>#<slot>` — `INSTANCE_FIELD/1#24`, `STATIC_FIELD/…`, `ARRAY_ELEMENT/…`,
`MAP_STATE/<rid>#-3` for a whole container. A rid is a per-run counter, so a state join is per
session.

**The pass-equality rule.** The identity is one function *and one input set* in both passes:
node attribution (`Attribution`'s three rules — explicit scope, innermost frame whose receiver
is a registered component, else the starter's node held by reference), the region frame set,
thread-start frames claimed at the work's first identity event, an index frame at every
application-scope method, loop frames, the producer endpoint and read/write site indexes. Any
new hook that pushes a frame or counts an event is woven in both passes or in neither. What the
identity deliberately does **not** tolerate: a different *number* of iterations of a loop on
the index path, and work started inside unwoven JDK internals (`Lost`).

## 5. Rows, and the composition

A replay publishes one row per event, one file per kind, into its own session directory, with
a manifest stating its role (`SEED` or `FOCUSED`) and, for a focused one, the obligation it
ran; every reference resolves in its own table.

| Row | States |
| --- | --- |
| `ActivationRow` | an occurrence ran: address, whether focused, whether instrumented (an ambient activation of an unwoven region has `instrumented=false`) |
| `DecisionRow` | a branch: site, ordinal, the jump's predicate as written at the site (polarity-free), `outcome`, and the clock readings its term rests on |
| `RootMintRow` | a declared root minted here: kind (`MARKER`, `INTEGRAL`, `CLOCK`), **the value this replay ran it at** (the plant where one followed), whether declared |
| `ReadRow` / `WriteRow` | a read joined to the version it observed or the placeholder it minted; a write with its version and expression |
| `ExportRow` / `AttachRow` | a message leaf left / arrived: endpoint, expression or minted `v_H`, the paired producer, the correlation id |
| `TargetRow` | the annotated site: the fatal predicate in the fatal polarity, whether that arm was observed, whether the anchor was reached |
| `ScheduleEvent` (`schedule.jsonl`) | the run's event order (§6); read by IMPORT as a session file, not a row |
| `GapRow` | a refusal or a diagnostic: kind, class, subject, detail |

`IMPORT` checks the invariants over the sessions handed to it and nowhere else: a session
states its role; one activation row per activation; a read has an observed version or a
concrete value, never neither; one symbol spelling and one sort per name; a root mint exists
only for a declared root; the target's term is in the fatal polarity; a flip is admitted only
if it took the other arm; a mint that RAN publishes its value, and an obligation whose mint
never ran is `NOT_ADMITTED`, not a blocker.

**A mint states what the region ran the root at.** A field mint reads its plant back from the
cell it stands on; a fresh-box mint (`RootMint.materializePrimitiveValue`: markers,
`LOCAL_DEFINITION`) states the box it handed the region. The composer holds one replay to one
value per root (`Composer`, "stated twice and differently"). A CLOCK is the exception by
design: every execution reads a clock fresh, so the focus row states a **skew** (`clockDeltas`)
and the replay adds it to its own instant — see to-do item 1, which is exactly the place this
rule and the previous sentence collided.

The composer aligns, merges, lowers and gates. For anchor `A` over admitted paths `p`:

```
exactly-one(selector_p)                                   ; target_path_partition
or(selector_p)                                            ; fatal_target
selector_p => pi_p /\ phi_p /\ reads_p /\ joins_p /\ valuation_p
selector_p => family(I)    for every interaction I that p's chain reaches
root domains, clock domains (one per declared symbol, floor = the reading), per-node monotone
clock chains, opaque-identity axioms
```

`pi_p` is the path's decision prefix strictly before the target observation, closed over the
writer and producer occurrences the path's joins reach (`Composer.closure`), each prefix cut at
the write or delivery that reached it. `reads_p` joins each read to the version it observed or
the placeholder it minted, else pins it to the recorded value, refusing if it can do none.
`joins_p` carries the boundary variables. `valuation_p` is what *this* path's replay ran each
varied root at.

**Families and world-compatible arms (DESIGN4 §3.4).** A family arm is `(producer path
condition, delivered expression)` guarded by the delivering replay's valuation of the roots that
expression depends on, and keyed by the **world** (the flips) it was collected in; a path may
only select arms whose worlds are compatible with its own. A wire arrival is bound by the
message it came in: one selector per (message, session), binding every leaf of the message at
once, with exactly one eligible session holding. An arm no session attests is
`UNATTESTED_ARM`. State families keep the writer occurrence as their unit.

**Flip queries and the nearest world (DESIGN4 §3.7).** `explore/FlipQuery` builds one query
per (path, decision): the path's prefix as it ran with the flipped decision negated (with a
60 s margin where it rests on a clock, `ClockMargin`), the arms of the handoffs it reaches, the
root domains and clock windows, and `(minimize Σ|x − recorded(x)|)` over the Int roots and
clocks it bounds. A term the lowering cannot state is refused by name — a prefix conjunct is
dropped with a gap, an arm is dropped with a gap, the flipped predicate itself refuses the
query — never wrapped into `(not )`. The model becomes the obligation's world
(`ObligationFactory`: `rootAssignments`, `clockDeltas` = model − the reading, `answers`,
`inheritedFlips`, `schedulePrefix`); a model that hands every root back its recorded value and
answers nothing is refused before a replay is spent.

`DECIDE` asks each composed path, alone and with every root free, whether it is satisfiable at
all (`PATH_SELF_CONTRADICTORY`, `DIAGNOSTIC` per path, `BLOCKING` when every path is inert).
`polarityDecides` requires the recorded valuation's disjunct to be unsat with a core naming a
valuation pin. The claim policy names the narrowest mechanism the evidence supports:

| Claim | What it means |
| --- | --- |
| `MARKER_FLIPPED` | a declared root moved inside its declared domain reaches the fatal arm (a configured source, or a transport fault marker) |
| `CLOCK_SKEW` | nothing declared moved; the fatal arm is reached only because clock cells sit elsewhere. The cells the model placed are the witness's moved roots |
| `MESSAGE_PAIRING_FLIPPED` / `STATE_PAIRING_FLIPPED` | every root stays; a different eligible, attested producer or writer delivers the read |
| `RECORDED_FAILURE_EXPLAINED` | the recording itself observed the fatal arm |
| `NO_SUPPORTED_WITNESS` | nothing in the corpus supports a witness. An answer, not an error |

**CONFIRM (DESIGN4 §5).** SAT says the model satisfies our formula; CONFIRM says the program
agrees. `explore/ConfirmMain` writes one focus row with `flip: null`: the world of the
obligation whose replay is the selected session (its `focused_task.jsonl` — root values, clock
skews, answers, mints — a world proven in an execution; the recording's own session planted
nothing and gets nothing), that session's schedule cut at the anchor, and `expected_edges.jsonl`
(the WIRE arm per selected message, the STATE join per read, the MARKER polarity per planted
marker, the ANCHOR). The replay's hooks compare and file `CONFIRM_MISMATCH`; `runtime/Confirmation`
decides; `accept/report.py` passes a case only with `confirmation.confirmed`. The model's own
re-solved instants are the published witness, not what the run is held to: a solver sits on the
boundary of its constraints and a run's timeline moves by more than that.

## 6. The schedule: a deterministic prefix, then the rest

The owner's design (2026-09-22): a focused replay's prefix must agree with the execution that
produced its task, so that `(r, c, i)` is stable, and attribution must not depend on hand-placed
probes in the workload. Non-goals: modelling shared-memory interleavings; changing the symbolic
semantics of compose; executing a witness to confirm it (CONFIRM was added later, in §5, and
re-runs a world a replay already ran).

**One new abstraction: `Event = (kind, c, site, k)`**, kind ∈ {START, CLAIM, SEND, RECV, WAKE,
END}: a task started / began running / a message left / arrived / a timed wait returned /
a daemon turn ended; `c` the causal context, `site` the static site, `k` the count of that
(c, site). No thread ids, no time. A run's schedule is the total order of its events,
`schedule.jsonl` per session (`recorded_schedule.jsonl` for the recording). SEND events also
state the producer endpoint the message carried, which is how `Corpus.senderOf` pairs a served
message with the occurrence that sent it (the control producer of §3).

**Recorder** (`runtime/ScheduleLog`, both passes): fed by the existing hooks — `Identity.startWork`
→ START, claims → CLAIM, the message doors → SEND/RECV, `beginTick`/`endTick` → WAKE/END — and by
the woven timed-wait stand-ins (`runtime/TimedWaits`: sleep, wait(long), parkNanos, await/poll
with timeout, plus notify/signal so that a signal is *state*: a woven signal marks the
longest-standing wait, an unmarked wait waits on).

**Enforcer** (replay only): the same class holds the task's `schedule_prefix.jsonl` and a cursor.
An event equal to the expected next one is admitted; otherwise the thread blocks until its turn;
nothing admitted for 15 s (`SCHEDULE_DIVERGED`) gives up the event that was waited for and
releases the waiters. Under a prefix, a timed wait uses virtual time (it returns at its turn), a
signalled return is the notifier's doing, an interrupt writes its WAKE where it stands. The
prefix is cut at the **target** of the task (path occurrence, focus, factor) — `explore/SchedulePrefix`.

**Past the prefix, the clock still holds** (rule 26): the concolic VM is many times slower than
the recording, so on the wall clock every daemon timer has expired at the cut and each tick fires
at once. `SchedulePrefix` therefore also writes `schedule_suffix.jsonl` (the rest of the order);
past the prefix `ScheduleLog` holds only the timeout WAKEs the rest names until every rest event
before them has happened or been given up; everything else runs free; a watchdog gives up the
open events before the earliest waiting WAKE; a turn's END settles its span; after two give-ups
(`REST_STALLS`) the rest is released. A run gone free leaves its waits to their own clocks.

**World inheritance**: an obligation's task carries the schedule of the session it was cut from
plus that session's planted values and inherited flips; a child of a NOT_ADMITTED session is
never cut (its path is a prefix nothing ran).

**Attribution** (`runtime/Attribution`, one lazy resolver, three rules in order): an explicit
scope (request / carried / inbound owner / tick owner); else the innermost application frame
whose receiver is a registered component (`CausynthCluster` registers every node's RPC servers,
namesystem, block manager, key managers, DataNode, SASL client/server, actors); else the
starter's node, held by reference. `ROLE.*` occurrences appear only when all three fail and are
reported as `LINEAGE_LOST`.

**Case-preparation rules the design needed on contact** (all general, all in
`experiments/hadoop/lib/README.md`): registration precedes any traffic; one request, one
scope; in-window per-node loops walk `CausynthCluster.dataNodes()` (sorted by registered name);
the block a case reads its roles off is pinned to a named node; each DataNode gets its own IPC
connections; nothing set up before the window may expire on the wall clock (idle-connection and
socket-cache timeouts set to 6 h); workload waits inside the window outlast the watchdog
(`WINDOW_WAIT_MS` = 60 s); scenario assertions before the anchor are `recordingPrecondition`s
(asserted only when not replaying); key rotations that must not close by daemon are explicit.
Known residue (a design non-goal): a daemon turn's *content* is clock/shared-state driven (a
held tick can carry heartbeat + IBR where the recording had one RPC).

## 7. Fault points, symbolic inputs, iteration (DESIGN 4)

[docs/design/DESIGN4-FAULTS-INPUTS-ITERATION.md](docs/design/DESIGN4-FAULTS-INPUTS-ITERATION.md)
is the current design; this is its summary.

- **Fault points (§1).** A fault is a decision at a transport door: every tree's
  `Client$Connection.sendRpcRequest` (IPC) and `SaslDataTransferClient.doSaslHandshake`
  (SASL) call `Debug.makeSymbolicBoolean("FAULT:<TRANSPORT>:<DIRECTION>")` unconditionally and
  throw on true. The marker is declared iff the case's `communication-mappings.jsonl` maps that
  transport (`WireFlowCatalog.declaredTransports`, `StaticScopeMap.declaredFault`). PLAN admits
  the firing occurrence as a declared site (`EXPLICIT_SYMBOLIC_FAULT` action, `LOCAL_DEFINITION`
  mint), the seed mints a MARKER root (recorded `false`), the branch on it is a symbolic decision,
  and `ClosurePlanner` makes every marker decision of a task — and of the control producer of the
  message it served — a flip site, proposed first. At the door `if (fault) throw`, the throw
  branch is the decision's `false` outcome and the solver assigns the marker `true` for it.
- **Symbolic inputs (§2).** The inputs of an occurrence are its declared roots, its declared
  region inputs, its wire attaches, and the reads of locations another occurrence wrote; each is
  a placeholder in the focused replay and is bound at compose to the arm that delivered it.
- **Iteration (§3).** Each wave writes `graph.jsonl` (nodes with their world, wire/state/thread
  edges) and `growth.jsonl` (`EXPOSED_REGION` rows: an occurrence reached by an admitted world
  inside a region that is in scope but not woven). The driver's `GROW` step
  (`campaign_grow`) runs `plan/ExposedRegionPlanMain` for the exposed regions, re-weaves, and
  re-runs the exposing obligation under the same world; the re-run session replaces the exposing
  one. Compose keys arms by world (§5). Epochs, the seed cache and every compat toggle are
  deleted. **Not yet exercised**: no run so far has exposed a region (to-do item 6).
- **CONFIRM (§5)** — see §5 above.

## 8. Preparing and running a case

### The host (as of 2026-09-23)

| what | where |
| --- | --- |
| this repository | `~/GraphChecker`, branch `refactor/deterministic-prefix`; `main` is the last accepted state |
| stock JDK 8 | `/usr/lib/jvm/java-8-openjdk-amd64` — `export JAVA_HOME=… PATH=$JAVA_HOME/bin:$PATH` before Maven (the environment's default is JDK 11 and the build refuses) |
| the concolic VM image | `third_party/OpenJDK-Concolic-Execution-Engine/build/linux-x86_64-normal-zero-release/images/j2sdk-image` (built; rebuild: `FULL_JDK=true JOBS=8 bash scripts/causynth_build_in_docker.sh` in that directory) |
| z3 4.14.1 | `~/.local/bin/z3` |
| Hadoop workload trees | `~/hadoop-hdfs-11741`, `-17897`, `-17899-bug1/2/3`, `-17960`, `-17967`, `-17967-b`, `-17967-c`; each on its `gc/<case>-v2` branch of `git@github.com:JHSUYU/hadoop.git` (committed, **not pushed**); `experiments/hadoop/<case>/tree-edits/` mirrors the edits |
| campaign hosts | `lift11`…`lift15` (ssh, BatchMode); at most two campaigns per host, the obligation workers of one campaign already fan out over the hosts named in the case's `workflow.properties` |
| snapshots | `~/gc-run/pNN` — a `git worktree` of one commit with its own built jar; a campaign runs from a snapshot so the working tree can move |
| outputs | `~/gc-out/accept-<round>-<case>/` (`summary.tsv`, `logs/`, `out/<case>/schedule/…`, `report/<case>/report.md`), `~/gc-out/launch-<round>-<case>.log` |
| scratch | `/localtmp/vnr3ne/graphchecker/` on each host (replay working directories) |

### Build and test

```bash
export JAVA_HOME=/usr/lib/jvm/java-8-openjdk-amd64 PATH=/usr/lib/jvm/java-8-openjdk-amd64/bin:$PATH
mvn -q -o package -DskipTests           # the jar: target/GraphChecker-1.0-SNAPSHOT-jar-with-dependencies.jar
mvn -q -o test                          # 143 @Test (keep it under 150; fold new behaviour into existing tests)
bash src/test/shell/run_engine_campaign_helpers_test.sh
```

`-o` (offline) is deliberate: `~/.m2` is NFS-shared and a Hadoop build in parallel with a Maven
resolve corrupted `maven-metadata-local.xml` once. Hadoop trees are built by
`experiments/hadoop/lib/run.sh <case dir> <case id> build` (installs the GraphChecker API and
shim into the local repository, compiles the tree with JDK 8, runs the workload test once
natively); build chains for several trees use `MAVEN_REPO_LOCAL` copies (`~/.m2b-repository`,
`~/.m2c-repository`) and `SKIP_GRAPHCHECKER_INSTALL=1`. **Never rebuild a tree while a campaign
runs on it, and never edit a running campaign's frozen inputs** (EMIT refuses "frozen input
changed").

### What a case declares

A case directory under `experiments/hadoop/` holds declarations only (`case.sh`,
`workflow.properties`, `target.yaml`, `symbolic-inputs.jsonl`, `root-domains.jsonl`,
`communication-mappings.jsonl`, `loop-bounds*.jsonl`); everything executable is
`experiments/hadoop/lib/` (its README lists the scripts and the workload rules). The loop-bounds
files key loops by Jimple unit id (`<method>#uNN`); **any edit to an instrumented method shifts
the ids after it** — re-read them from `region_skeletons.jsonl.gz` (`loopControlSiteIds`) after
a tree edit. Per-case notes: `experiments/hadoop/<case>/README.md`.

### A round

```bash
# 1. snapshot the commit you want to run (from ~/GraphChecker, tree clean and committed)
git worktree add ~/gc-run/p24 HEAD && (cd ~/gc-run/p24 && mvn -q -o package -DskipTests)
# 2. launch: two cases per host, the rest queued behind them
tools/rounds/queue-launch.sh /u/vnr3ne/gc-run/p24 v21 \
    lift12:hdfs-17899-bug3,hdfs-17967-pathA lift13:hdfs-17899-bug1,hdfs-17967-pathB:hdfs-17967-pathC \
    lift15:hdfs-17899-bug2 lift11:hdfs-11741,hdfs-17897:hdfs-17960
# 3. watch: one DONE line per finished campaign (exit, seconds, claim, blockers, verdict, moved roots)
tools/rounds/round-monitor.sh 'v21-*' | grep --line-buffered "DONE "
# 4. stop one run: the launcher log names its process group
ssh lift12 "kill -TERM -$(grep -o 'process group [0-9]*' ~/gc-out/launch-v21-17899-bug3.log | awk '{print $3}')"
ssh lift12 "pkill -TERM -f 'gc-run/p2[4]'"    # the driver keeps spawning obligation JVMs; kill those too
```

`tools/rounds/launch-run.sh` is what each host runs (it sets `JAR`, `CASES`, `OUT`, `Z3_BIN`,
`CAUSYNTH_CUSTOM_JDK_HOME`, `SKIP_BUILD=1` and execs `experiments/hadoop/accept/accept.sh`).
Campaign durations at two per host: 17960 ≈ 5 min, the block-key cases 12–25 min, 11741 up to
an hour. The acceptance rule is in `experiments/hadoop/accept/README.md`: `SAT_CANDIDATE`,
`FINAL_READY`, no BLOCKING gap at any stage, the case's expected mechanism (`EXPECTED_MECHANISM`
in `report.py`: 17960 `MARKER_FLIPPED` on `SNAPSHOT_DELETION_ORDERED=false`, the others
`CLOCK_SKEW` or `MARKER_FLIPPED`), `polarityDecides`, non-empty `movedRoots`, and
`confirmation.confirmed`. A PASS line is not acceptance on its own: check that the witness
*needs* the roots it moves, that handoff leaves do not collapse distinct arrivals
(`attaches.jsonl`: same symbol, different arrival), that the fatal was observed in a replay, and
that clock values are plausible under a monotone floor. The last accepted round was judged by an
assessor plus two skeptics per case on exactly those four checks.

## 9. Status (2026-09-23, evening)

**Accepted: 9/9 on `main` = `497dc8beb` (round v15, 2026-09-23 02:00).** 17960
`MARKER_FLIPPED` (`ordered=false`); 11741, 17897, 17899 bug1/2/3, 17967 A/B/C `CLOCK_SKEW` with
`polarityDecides`, each witness needing the NameNode rotation clock plus the stale node's
refresh clock. That commit has the deterministic prefix, the rest clock, attribution, the
window rules and no fault markers; `main` is **not pushed**. Its outputs are
`~/gc-out/accept-v15-*` (keep them: they are the reference corpora).

**Design 4 is implemented and merged on `refactor/deterministic-prefix`** (HEAD `e23a548cc`
plus this documentation commit): fault markers end to end, control producers, `graph.jsonl`/
`growth.jsonl` and `GROW`, world-compatible arms, clock domains per symbol and per-node
monotone chains, CONFIRM, the nearest-world objective; epochs, the seed cache, `FaultMarker`,
`ScheduleReportMain`, the scalar-projection codec and every compat toggle deleted. 143 unit
tests and the shell test are green at every commit. **It is not accepted yet**: the debug rounds
v16–v20 found and fixed nine general defects (below), and at the time of writing the round v20 on
snapshot `~/gc-run/p23` (`e23a548cc`) stands at: **17960 PASS on p22** (`77240f66e`, v19,
confirmed) but **`SAT_UNCONFIRMED` on p23** (to-do item 3); bug3 / 17897 / pathA / pathB /
pathC / bug1 **FAIL** with the open defects of to-do items 1–2 (no session observed the fatal, or
the fatal was observed with nothing planted); 11741 and bug2 were still running — read
`~/gc-out/accept-v20-*/summary.tsv` for their final state. Snapshots `p17`–`p23` are worktrees
of the commits named below; `p17`–`p20` can be removed.

Fixed during the D4 debug (each general, each a commit on the branch):

| round | defect | fix |
| --- | --- | --- |
| v16 | the door hunk shifted Jimple unit ids; loop-bounds rows named stale `#uNN` | ids re-read from the skeletons (`a8bce012c`) |
| v16 | a door fault was admitted for a case that maps no transport (17960 planned its unregistered client) | declared iff the transport is mapped (`c1cb49cb9`) |
| v16 | fault flips were never proposed: the sender of a served message is reached by no data edge | control producers in the closure (`a40e1e3b9`) |
| v16 | pre-window activations reached the trace (the start-paused guard had been deleted as a "toggle"): `OCCURRENCE_ADDRESS_SHARED` everywhere, 17960's config hook "fired under none" | the trace states the window only (`34ddf099c`) |
| v17 | CONFIRM planted the model's re-solved values and clock instants: anchor reached, fatal not observed | CONFIRM re-runs the selected session's own obligation world (`cbf54ca7d`) |
| v18 | a fresh-box mint stated the live read under a plant: every fault-flip session refused by the composer | the mint states what it ran the root at (`cbf54ca7d`) — see to-do 1 for its clock side |
| v18 | a `ROLE.*` endpoint carried the pooled handler's start iteration: 17960's seed reached no target after one heartbeat shifted the rotation | role occurrences indexed from the scope root (`77240f66e`) |
| v18 | z3 answered boundary points (+30 days): nested obligations' inherited flips failed, no fatal path | the nearest-world objective (`e23a548cc`) |
| v18 | an arm conjunct lowering to `(not )` made z3 reject whole queries | the arm is dropped by name (`e23a548cc`) — see to-do 2 |

**2026-09-23 night, round v21 on `~/gc-run/p24` = `a20f56191`** (the three fixes of the
former to-do items 1–3: a CLOCK mint states its reading, an arm keeps its statable conjuncts and
a paired-unstatable handoff is refused, CONFIRM's MINT edges and the placeholder join held by
its writer): **hdfs-17899-bug3 PASS** (`CLOCK_SKEW`, `polarityDecides`, five clock cells moved,
0 gaps, 1448 s) — the nested-clock defect is fixed. **17960 FAIL at REPLAY** after 203 s: the
seed replay left its schedule prefix at position 194 of 247, which it has done in *every* round
v18–v21 (positions 207/207/234/194); v19/v20 reached the target afterwards by luck, v21 did not.
The cause is three general defects of the enforcer, diagnosed event by event in §14 D3 and fixed
by to-do item 1 below. bug2, 11741, pathA/B/C were in waves 2–5 and bug1 in wave 1 at the time
of writing; 17897 queued — read `~/gc-out/accept-v21-*/summary.tsv`. The whole source was read
on the same day (owner's rule, §12); its notes are §14, and the to-do below is re-ordered from
them.

## 10. The to-do, in order

Work from the top; each item states its evidence and where the fix goes. Items 1–3 are what
stands between the branch and a 9/9 accepted round; item 4 is the cleanup the read of §14
found, in two halves (now, and after 9/9); after that `main` moves and the parked housekeeping
is due.

1. **The schedule enforcer: one order, one rule** (§14 D3; blocks 17960 at REPLAY and pathA at
   CONFIRM in v21, and sits under every `SCHEDULE_DIVERGED` of v18–v21). Today `ScheduleLog`
   holds a replay in three regimes — the prefix strictly, event by event; on the first event that
   does not come within 15 s it abandons the *whole* prefix to the rest; the rest holds timeouts
   only — an event whose key the prefix does not hold at all waits for the watchdog, and a `WAKE`
   is written whether a timeout or an interrupt ended the wait. On 17960 the recording's prefix
   holds a SEND the replay can never make (an IPC attempt on a connection that turned stale
   between Hadoop's two `shouldCloseConnection` checks, retried outside the weave), so the order
   was abandoned 53 events before its end; in v20 the event came, just >15 s later
   (saveNamespace on the concolic VM), and the wall-clock watchdog called it a divergence; the
   old NameNode's daemons, interrupted by `stop()` in the recording, were "woken" by virtual time
   in the replay and ran an iteration more. The fix, in `contract.ScheduleEvent`,
   `runtime.ScheduleLog`, `runtime.TimedWaits` and `runtime.Identity`:
   - `Kind.INTERRUPT`: a timed wait the workload's interrupt ended. Written when it happens,
     never held, never made by virtual time; a held wait takes a turn only at a `WAKE` slot.
   - One list of slots — the prefix, then the rest, the cut between. An event takes the earliest
     slot of its key `(kind, c, site)` that is OPEN or GIVEN_UP; with none it runs free at once
     (counted, never held). A slot before the cut, or a `WAKE` slot anywhere, is held until every
     earlier slot is settled; any other slot past the cut is taken at once.
   - Two settlements. A turn's `END` gives up what the turn did not do (as today: the event may
     still come, and then takes its slot). An occurrence's CLOSE (`Identity.regionExit` of the
     entry that opened it) settles every OPEN slot of that occurrence as DEAD: it cannot come any
     more, so no later event of the key takes it — the v21 stale SEND belongs to occurrence
     `1c0a…`, which closes before the retry opens `4550…`, so the retry's SEND takes its own slot.
   - The watchdog: nothing settled for the timeout while some thread waits for a turn **and the
     threads not waiting used less than half a CPU over it** (`ThreadMXBean`) → every OPEN slot
     before the earliest waiting slot is GIVEN_UP, stated `schedule#<slot>` before the cut (the
     subject CONFIRM's rule (a) reads) and `schedule-rest#<slot>` past it; so that it never blocks
     for good, 8× the timeout with nothing settled fires whatever the CPU; after `REST_STALLS`
     give-ups past the cut the rest is let go.
   - Deleted with it: the prefix→rest jump, the `freeRun`/`timeouts` pair, `ASK_FRESH_MS`, the
     doors `tryObserve`/`awaitTurn`/`admitNow` (one blocking door, one polling door remain), and
     the interrupted admission that never advanced the cursor. `ScheduleLogTest` follows the rule.
   Then a fresh 17960 recording + seed replay must admit its prefix to the end with no watchdog
   give-up, and pathA's CONFIRM is judged again.
2. **bug2's IMPORT death: a mint's own store published as somebody else's write** (§14 D1/D2).
   `RowRuntime.declaredMintSymbol` is filled *after* `api.symbolizeField` made the fresh-box
   store, so an activation that closes in between reads the store out and publishes it as a
   `WriteRow` at its own site, and invariant 7 refuses the session as a fabricated write. Fix:
   register the mint before the store (keyed by the label the VM spells,
   `M_<sort>_field_<label>`), make `RowPlaceholderMint.declaredMint` one test (the register),
   and key invariant 7 by the placeholder's `(location@mintVersion)` rather than by symbol.
3. **Read v21 to the end, then finish the round**: v21 on p24 PASSED bug1, bug3, pathB, pathC
   and 17897; pathA is `SAT_UNCONFIRMED` (CONFIRM left the selected path's schedule — item 1);
   17960 died at REPLAY (item 1); 11741 and bug2 were still running. Place the next round by
   memory (§12): each lift has 30 GB; 11741's obligation workers each load the whole corpus
   (1.5–5.5 GB per solver JVM in wave 2, growing per wave), so 11741 runs alone on a host with at
   most 3–4 workers, the light cases at most two per host, the head (lift11) lightest. Any FAIL is diagnosed by §11 before a fix; `PATH_SELF_CONTRADICTORY` on
   every path still means no session observed the fatal. Then all nine on one snapshot, the
   acceptance checks of §8, and `main` fast-forwarded to that commit.
4. **The cleanup the read found (§14, R-items).** *Now, before the round* — each after `git
   grep` for readers, one commit per package: the dead members and second spellings (R1, R3,
   R8, R11, R12, R23, R25, R27–R29, R31, R35–R37, R40, R42, R43, R45, R47, R49, R50, R55–R57,
   R59–R65) and the fallbacks that become refusals (R6, R20+R51, R24+R54, R44, R46). *After
   9/9* — the structural ones: one thread context instead of three stacks (R18), fold
   `VmLoweringCore` into `SmtLowering` (R58), decide the refined graph (R48, R14), delete
   recording pass 1 (R13), `transferKind` (R32), and the D4 review plan (item 9).
5. **Memory per obligation worker.** `ObligationSolverMain` calls `Corpus.read(iteration, …)`
   for one obligation, so every worker holds the whole corpus and a wave of 8 holds it 8 times
   (lift11, 11741 v21 wave 2: 26 of 30 GB used and 9 GB swapped). Either a worker reads only
   the sessions its obligation's world and arms need (the family-arm rule reads every session
   that states the family — check `Arms` before narrowing), or a slot claims its next obligation
   only when its host has the memory for one (`campaign_wave_slot`, `/proc/meminfo`
   `MemAvailable`, a reserve the case states). Until then the round is placed by hand (item 3).
6. **Exercise GROW end to end.** `growth.jsonl` has had 0 rows in every run so far. Either no
   admitted world reaches an unwoven region in these nine cases, or `WaveGraph.writeGrowth` never
   sees one: it requires an activation row (`instrumented=false`) inside `corpus.upstreamOf(
   focused, factor, session)`, and `instrumentSkeletonRegions` weaves the entry hook at every
   skeleton root only, so a region no skeleton names has no hook at all (R53). Write an
   `ExploreTest` whose target is reached only through a replay-exposed region and settle which of
   the two DESIGN4 §3.3b means (bug1's catch path is the intended case).
7. **Housekeeping the owner asked for and then parked (2026-09-23 morning)** — do it only when
   asked again: delete old outputs (`~/gc-out/accept-v16..v21-*` once superseded) and snapshots
   (`git worktree remove ~/gc-run/pNN`); rename the Hadoop branches `gc/<case>-v2` → `gc/<case>`
   ("there is no v1/v2, the current code is the code"), delete the stale remote branches, push
   both repositories; the GraphChecker code lives on `main` only.
8. **Owner follow-ups noted at v14/v15, not blocking**: the composer's `clock_domain` is asserted
   per cell for only the last session's symbol (bug1 had three rotation-2 expiry roots with no
   domain, wrapped by z3 to ±9.2e18; they do not decide the fatal); the published valuation could
   prefer the forward-only witness (a backward clock value is a solver's choice, never a
   mechanism); a message-driven DataXceiver turn is held like a timer tick past the prefix
   (documented in `ScheduleLog`).
9. **The rest of the D4 review plan** (from the deleted REFACTOR-D4-PLAN, phases 4–7; none of
   it changes behaviour, all of it reduces the 82k lines): split `ConcolicRegionRuntime` and move
   the offline aggregator (`RuntimeRegionPlanner`, `RuntimeRefinedGraphBuilder`,
   `OccurrenceBinding`) out of the workload-JVM surface; one `Declarations` authority in PLAN and
   one loop-bound decoder; one `World` value type and one admission rule in EXPLORE, `Corpus`
   split into corpus view / world index / lowering cache; one declarative case manifest and
   `run_engine.sh` split by stage. Deferred identity items: `Lost` should address to an empty
   index; carry lineage explicitly instead of `InheritableThreadLocal` (= R18); loop bodies get
   their own iteration frames.
10. **The offline gate** `tools/gate3/` has not been maintained since the D4 refactor (its
   corpora and commands predate `schedule.jsonl` and the obligation directories). Either re-point
   it at the v15 corpora and make it pass, or delete it; today the acceptance round is the gate.

## 11. Debugging a round

Where to look, in order, for a FAIL line:

1. `summary.tsv` — `claim`, `finalStatus`, `blockers`, `reason`. `MISSING` means the campaign
   died before EMIT: `logs/<case>.log` has the stage (`[campaign:error] stage=… reason=…`); a
   `REPLAY` death points at `iteration-0000/seed-result/focused/replay.log` and the seed
   session's `gaps.jsonl` (`SCHEDULE_DIVERGED` with the prefix position, `TASK_UNANSWERED` with
   why the planned occurrence was not matched).
2. `out/<case>/schedule/final/gaps.json` — `byStage`/`byCode`, then the BLOCKING rows' `detail`.
   `PLAN OCCURRENCE_ADDRESS_SHARED` = two activations, one address: the identity or the window;
   `COMPOSE PATH_SELF_CONTRADICTORY` (all paths) = no session observed the fatal: go to the
   obligations; `UNSTATED_VALUE "stated twice and differently"` = a mint and its obligation
   disagree; `FORMULA_SAT_AT_RECORDED_VALUATION` = a path reaches the fatal with nothing moved.
3. `iteration-0000/obligation_results.jsonl` and the per-wave `obligations-NNNN/*/` — count
   verdicts per wave (`ADMITTED` / `UNSAT` / `NOT_ADMITTED`) and read the `NOT_ADMITTED` details:
   "wrong decision at … took X, the flip this replay INHERITED …" is a world that does not
   reproduce (compare the child's and parent's `focused_task.jsonl` and the two sessions'
   `decisions.jsonl` clock readings at that site); "the solver did not decide" with a z3 error is
   a malformed query (`obligation_query.smt2`, `stdout.log`/`stderr.log`); "the focused prefix
   reproduced and …" is an admitted flip. The same obligation id is stable across runs of the
   same recording, so a v15 directory is a direct baseline.
4. `sessions/<id>/` — `targets.jsonl` (`observedFatal`, `reachedAnchor`), `decisions.jsonl`,
   `roots.jsonl` (what each mint ran at), `schedule.jsonl` vs `recorded_schedule.jsonl` (print
   both around a divergence position: kind, site, context, k, endpoint).
5. `final/claim.json` (`valuations[]` with status, unsat core, selected path/session,
   `fatalObserved`), `candidate_composition_manifest.json` (paths and which observed the fatal),
   `compose.log`, `confirm.json`.

Recipes that have paid off: a query can be re-solved by hand (`~/.local/bin/z3 -smt2 -T:120
file.smt2`) after editing — that is how the nearest-world objective was validated in one minute;
`-Dcausynth.debug.producers=true` via `CAUSYNTH_WORKLOAD_JAVA_OPTS` prints every send's full
producer endpoint in a replay, and the recording's is on its `EXCHANGE_SEND` row in
`runtime/runtime_trace.jsonl` — diff the two when anchors drift; `UNATTESTED_ARM` → the attach's
producer → `tasks.jsonl` → the plan → the trace's `METHOD_ENTER` for the missing occurrence →
the finalizer's admission; a schedule with `WAKE …waitForWork` or `RpcRequestSender.run` right
after a divergence or a short prefix means released waits, not real timeouts.

A schedule divergence is read by ALIGNING, not by the one line the turnstile prints: load
`recorded_schedule.jsonl` (or the worker's `schedule_prefix.jsonl`) and the session's
`schedule.jsonl`, keep the rows with a `kind`, compare `(kind, context, site)` position by
position to the first mismatch, then for the expected event count how many events of its key the
replay made at all (0 = an event the replay never makes: D3a; the same number as the recording =
it came late: D3b); the `mark` rows (`{"mark": occurrence, "at": position}`) of both files say
which occurrences opened where, so a missing SEND's occurrence can be followed to its region;
`occurrence`/`endpoint` on the SEND rows join to the recording's `EXCHANGE_SEND` trace rows
(`correlationId` is Hadoop's call id). This is how §14 D3 was found in an hour after four rounds
of reading the printed line.

Traps: zsh is the login shell here — `echo ====` fails (`=` is path expansion), unmatched globs
abort the whole command, `set -- $spec` does not split, `PIPESTATUS` is `pipestatus`; write
monitor and launcher scripts in bash. A `pkill -f` pattern that appears in your own ssh command
line kills the ssh session (`gc-run/p2[3]` style patterns). A heredoc piped to a loop of `ssh`
needs `ssh -n`. Killing a campaign's process group does not stop the obligation JVMs the driver
keeps spawning — kill by the snapshot path too.

## 12. Working rules

The owner's standing rules; every one of them has been paid for.

- **Read the whole source before fixing, and fix from the whole** (owner, 2026-09-23
  afternoon): "把所有 source code 读一遍；修 bug 不能每次只修当下，要在全局视角下思考，防止
  bug 一个接着一个；整体设计要 general、简洁；死代码、fallback 代码一个不留." The D4 debug
  rounds fixed nine defects one at a time and each fix exposed the next (the arm-drop rule of
  `e23a548cc` turned a z3 syntax error into a spurious SAT at the recorded valuation). So: before a
  change, know every consumer of the notion (grep and read, not guess); state the rule in its one
  place; when two places answer one question, delete one; a fallback, toggle, second spelling or
  unread field is deleted on sight. Reading the tree package by package (contract → runtime →
  plan → causynth → explore → compose → smt → shim → `run_engine.sh`) is the standing
  prerequisite for anyone taking this over; the notes of that reading are §14.
- **General fixes, never per-case.** Hadoop edits are allowed, but as one canonical
  instrumentation set for every tree and one workload rule set; a fix is stated for its whole
  class and traced rows → explore → compose → claim.
- **Delete, don't adapt.** No compat layers, fallbacks, toggles or second spellings; a superseded
  mechanism is removed outright (list its readers with `git grep` first).
- **One implementation per notion.** Two places answering one question is the defect.
- **The rows are the authority; refuse by name.** A question the corpus cannot answer is a
  registered gap, never a default, cap, heuristic or synthesized value.
- **Big strides, then debug.** Write the whole main body of a design first (compile only), run
  the unit suite at merge time, then debug with campaigns as one phase — a round costs 15–60 min
  per case and the design spans five packages.
- **A fresh recording is required** to judge a runtime fix; re-composing an old corpus reads
  rows made before the change.
- **Balance memory across the lifts; never blow one up** (owner, 2026-09-23 15:30). Each lift has
  30 GB RAM and 48 CPUs; check `free -g` everywhere before a launch and place by measured need
  (§10 items 3 and 5). A running campaign that over-commits is capped between obligations —
  SIGSTOP the wave's extra slot subshells, resume them once the queue is claimed — never by
  stopping a running JVM (z3's wall-clock timeout would fire).
- **Never**: `git add -A` (`experiments/hbase` is unrelated and untracked); edit a running
  campaign's inputs or scripts; rebuild a tree under a running campaign; push without the owner's
  approval; claim a PASS from the claim kind alone (§8).
- Keep the unit suite small (143 `@Test`); unit-test assertions that stand in the way of a
  correct change may be removed.
- Reply to the owner in Chinese, briefly, with progress and evidence.

## 13. Repository map and documents

```
src/main/java/edu/uva/liftlab/graphchecker/   the engine (§3's package table)
src/shim/                                     the hadoop-shim jar the trees call
src/test/                                     143 @Test + src/test/shell/run_engine_campaign_helpers_test.sh
run_engine.sh                                 the campaign driver
experiments/hadoop/<case>/                    declarations + README + tree-edits/ per case
experiments/hadoop/lib/                       the one harness every case runs through (README: workload rules)
experiments/hadoop/accept/                    accept.sh, probe.sh, report.py (README: what PASS means)
tools/rounds/                                 queue-launch.sh, round-monitor.sh, launch-run.sh (§8)
tools/gate3/                                  the offline gate, unmaintained (to-do 10)
third_party/OpenJDK-Concolic-Execution-Engine/ the concolic VM (in tree)
docs/CONCOLIC_INTEGRATION.md                  the VM boundary: broker ABI, capabilities, refusals
docs/design/DESIGN4-FAULTS-INPUTS-ITERATION.md the current design (fault points, inputs, iteration, CONFIRM, nearest world)
docs/design/LEAN-DESIGN.md                    the fixed one-page design frame the README restates
docs/design/IDENTITY-V3.md, IDENTITY-IMPL.md, IDENTITY-V2.md, INTERACTION-ID.md  the identity designs the code cites (§4)
docs/design/CLOSURE-V2.md                     the scoping walk the code cites
docs/design/CONTRACT-SPEC.md                  the row/gap contract the code cites (its package names predate the current tree)
```

The design documents are kept verbatim because the code cites them by section; where this
README and one of them disagree, the rows decide. The owner's schedule/attribution design of §6
and the case-preparation rules are not in `docs/`; §6 and `experiments/hadoop/lib/README.md`
are their record.

## 14. The whole-source read (2026-09-23): defects, redundancy, and the order to fix them

Read package by package on 2026-09-23 under the rule of §12 (contract, runtime, plan,
causynth, smt, explore, compose, shim, `run_engine.sh`, `experiments/hadoop/lib` and
`accept`, `tools/rounds`, one case directory, the tests). Every item names its file, so
`git grep` verifies it; nothing here is fixed until §10 says so. D = a defect that costs a
case; R = redundancy, dead code, a fallback or a second spelling, which the owner's rule
deletes on sight after its readers are listed.

### Defects

- **D1/D2 — bug2's fabricated write** (`runtime/RowRuntime`, `RowPlaceholderMint`,
  `contract/RowInvariants`). v20's IMPORT death was invariant 7 on `writes.jsonl` (INSTANCE
  204.24@855): the marker's fresh-box mint store was published as a `WriteRow` by another
  activation at `GeneratedMethodAccessor#invoke#40:WRITE` while the placeholder row states the
  same `(location, mintVersion)`. `RowRuntime.declaredMintSymbol` is filled in
  `ActiveRegion.recordManualSymbolization`, *after* `api.symbolizeField` made the store, so an
  activation closing in between reads the store out. Invariant 7 keys the rule by SYMBOL (any
  write whose whole expression is a placeholder symbol) rather than by the placeholder's
  `(location@mintVersion)`, so a legitimate copy `x.f = <mint symbol>` would be refused too.
  `RowPlaceholderMint.declaredMint` answers one question three ways (raw symbol match,
  `endsWith("_field_"+requested)`, the register). Fix = §10 item 2.
- **D3 — the schedule enforcer** (`runtime/ScheduleLog`, `TimedWaits`, `contract/ScheduleEvent`).
  Evidence, v21 17960 seed replay (`~/gc-out/accept-v21-17960/.../iteration-0000`): the prefix
  and the replay agree event by event up to 152; prefix 150–152 are `WAKE k=0` of the old
  NameNode's `NameNodeResourceMonitor`/`EditLogRoller`/`LazyPersistFileScrubber` (intervals
  5 s / 5 min / 5 min, all three consecutive — the interrupt of `nn.stop()`), which the replay
  admitted by virtual time and then wrote again as `k=1` when the real interrupt came (D3c);
  prefix 194 is `SEND HADOOP_IPC#REQUEST` of occurrence `1c0a69122e9cc27e` (Hadoop call 20, no
  `sendRpcRequest#u5` START after it, no RECV of its endpoint anywhere): `Client.sendRpcRequest`'s
  door fires after `if (shouldCloseConnection) return` and before the `offer` loop that checks
  it again, so the recording's attempt on the connection to the stopped NameNode went through
  the door and nothing else, failed, and `RetryInvocationHandler` (outside the weave) retried as
  call 21 = prefix 201 = the replay's first SEND (same occurrence `4550c63f9863c53e`, same
  endpoint); the turnstile waited 15 s for 194 and handed the other 52 events to the rest (D3a).
  v18/v19 diverged at a `RECV HADOOP_IPC#RESPONSE` under an `Anchor:` the replay never mints
  (0 events of that key in the whole replay) — a message key embeds the producer endpoint
  digest, so one missing attempt makes the whole exchange unnamed. v20 diverged at a SEND the
  replay *did* make, all three of that key, the third >15 s after the previous admission while
  a daemon's held sleep was asking (D3b). Also seen: an unwoven daemon (`HeartbeatManager` is
  outside the 17960 scope; its `beginTick` is the shim's hand call, its `sleep(5000)` the wall
  clock's) ticked inside the slow replay's restart with a key the prefix does not name and was
  held until the interrupt released it. Attribution was consistent (the tick at prefix 157 is
  the new NameNode's monitor, started by `startCommonServices` inside the `restart-namenode`
  scope, matched by replay 162); the woven class sets of recording and replay are identical.
  Latent in the same code: an INTERRUPTED admission never advances the cursor even when its
  event is next. Fix = §10 item 1.

### Runtime

- R1 `RuntimeTraceContext.enterRoot`: `Seed seed = null` and every `if (seed != null)` are dead.
- R2 `WireExport.attachLeaf`: the `site == null` branch says "the run says so" and returns silently.
- R3 `HandoffMint`: stale "D2 … (M2)" comment and the `HANDOFF_MINT_PREFIX` doc block.
- R4 `RowRuntime.clockCell` is filed twice (mint and rootMint); keep the mint's.
- R5 `ScheduleLog`: five admission doors (`observe`/`tryObserve`/`turn`/`awaitTurn`/`admitNow`)
  and two enums (`Admission`, `Turn`) for one turnstile — folded by D3's rule.
- R6 `ConcolicRegionRuntime.parseJson`: malformed JSON falls back to `GSON.toJsonTree(value)`;
  refuse by name. R7 `statesTargetReach`, `lightweightAccessorContext*`,
  `materializeSymbolicBoolean` (always false; the marker's value is the plant at
  LOCAL_DEFINITION): check readers, rename or delete.
- R8 `ActiveRegion`: empty javadoc fragments; `threadName` and `vmContextId` readers?
- R9/R18 three thread-context stacks for one thread (`Identity.CURRENT`,
  `RuntimeTraceContext.CURRENT`, `Lineage.STACK`, two of them `InheritableThreadLocal`) carry
  overlapping facts (scope, source, lineage): the largest structural redundancy in runtime and
  the README's deferred "carry lineage explicitly" item.
- R10 `Obligation.unproducible` invents only an UNPAIRED arrival (by design; keep).
- R11 `ConcolicTaskPlan.RuntimeTask`: `replayGroupId`, `topologyEpoch` (doc cites the deleted
  linked replay), `observedSemanticAnchorIds`, `admittedTurns`, `loopBoundGapClaimed`,
  `requestContexts` (write-only), `attachPortIds` — readers, else dead.
- R12 `RuntimeRegionPlanner.putRecordedTraceIds` keeps laneId only; `MethodEvent.reattribute`
  (called?); the `ANCHOR_*` kinds are validated in `RootContextSelector.from` and never read.
- R13 `CausynthTraceRecorder` pass 1 (`enterMethodLite`/`exitActiveMethodLite`) — delete after
  diffing the occurrence-address sets of the nine recordings (§10 item 9); R14/R48 the field
  trace feeds `RuntimeRefinedGraphBuilder`, which IS read: `RuntimeSelectedRegionFinalizer.
  finalizeRegions(refinement.rows …)` → `StaticProgram.edgesByRegion` and `RegionDemandIndex`
  read `method`, `kind`, `toCell`/`fromCell`, `transferKind`, `guardSiteId`, `regionIds`; the
  refiner stamps `regionIds`, `runtimeFieldBindings`, `fieldPath`, `runtimeObserved`, `graphKind`
  and the binding rows. Before deleting it, show that the candidate graph + skeleton lookup gives
  the finalizer the same rows (the `regionIds` annotation is already recomputed there).
- R15 switch support is real on both halves (`instrumentConcolicSwitch`, `RESOLVE/RECORD_SWITCH_
  BRANCH`); unexercised by the nine cases; keep.
- R16 `SymbolizeAction.symbolicName`/`rootKind`/`replayOccurrence` readers?;
  `LoopRootInvocationContext.ordinalByTaskId` values unread (`containsKey` only).
- R19 `FocusedReplay.focused(taskId, address)` keys FOCUSED_OCCURRENCES by `render()` while the
  other sets key by `id()`: two spellings of one join.

### Plan

- R20 `StaticScopeMap.readRegions` catches every exception and returns an empty map ("falls
  back to comparing region ids"); PLAN always writes `region_skeletons.jsonl.gz` beside the map
  in one stage (`CausynthArtifactWriter`): require it, refuse by name. Its consumer is R51.
- R21 `DeclaredSiteCapture.accessorPort` publishes the receiver object id under four names
  (`rootObjectId`, `receiverObjectId`, `fieldReceiverObjectId`, `objectId`) and the ordinal under
  three; R22 it writes `fieldPath` and `fieldPaths=[fieldPath]` and `ExecutionTask.
  compactInputActions` deletes the second when equal. One spelling each (readers:
  `SymbolizeAction`, `FieldAccess`).
- R23 `LoopBoundPolicy.toJson` writes `maxBackedgeTraversals`, which nothing decodes.
- R24/R54 `SelectorResolution.resolve` returns a DEGRADED address (node `unresolved`) for a
  selector that matches nothing; `ComposeMain.anchorOf` uses it and answers
  `DECLARATION_MISSING`, while `ExploreMain.root()` refuses the same situation by name and
  `RuntimeWorkflowDiscovery.declaredTarget` already refuses it at PLAN. One rule: refuse by name.
- R25 `CommunicationCatalogContract.SERVER_ENTRY_CANDIDATES` is always a singleton of
  `serverEntryMethod`. R26 `SharedFieldFlow.LOCATION_MATCH_AUTHORITY`/`EDGE_LOCATION`/`fieldKey`,
  `BranchPredicateAlgebra.complementOperator`, `VmExpressionTable.Store.importField`,
  `MapFields.object/booleanValue/safe/firstNonEmpty` — readers?
- R27 `DependencyRole` has one value (`VALUE_FRONTIER`) on every port; R28
  `ConfiguredSourcePhaseContract.Phase` has one value and the rows carry `phaseKind` = phase and
  `ownerCallId` = `enclosingCallIds[0]`, validated equal: facts stated twice. R29
  `RuntimeWorkflowDiscovery.RankedWorkflow` ranks nothing. R30 `ConcolicScheduler.
  scheduleLoaded` recomputes `declaredLoopBounds` per selection. R31 `ExposedRegionPlanMain`
  adds a SKELETON row to a SYMBOLIC_REGION catalog (works, two row kinds in one list).

### Causynth

- R32 `StaticDataflowEdgeSchema.transferKind`: VALUE_TRANSFER vs UNKNOWN is decided by
  lower-cased text sniffing (" encode", "serialize", "stringbuilder", map ops…); readers ask by
  name only for GUARD, EXCEPTION, HEAP_WRITE, HEAP_READ, VALUE_PASS, DYNAMIC_DISPATCH.
- R33 `WireFlowCatalog.declaredTransports()` is a second, static-cached read of the mapping file
  beside `fromConfiguration()`. R34 `CfgLoopControl` BY_BODY cache/`forget()`, `NaturalLoop.
  terminals/exitEdges/identity`, `Backedge.identity` — readers?
- R35 `SymbolicRegionPlanner.selection` values: only `startsWith("EXCEPTION")` is read;
  `StaticProgram.regionEdges` is cleared and never filled; the `planGaps` javadoc cites
  truncation gaps that no longer exist. R36 `RegionRow.graphKind/branchPolicies/outputs/
  symbolicInputs/runtimeOccurrenceIds` readers?
- R37 `RuntimeSelectedRegionFinalizer`: `DeclaredFieldCell` has no reader; `readOccurrences`'s
  return value is ignored; five javadoc fragments without a member; `RegionDemandIndex.
  fatalSeeds` is a documented fallback ("generic exception cell … for a region without an
  explicit failureTarget policy") that `failureDirectedClosure` makes unreachable by refusing
  `FATAL_TARGET_POLICY_ABSENT` first — delete.
- R39 `CommunicationCatalogPlanner` publishes one `LOOP_EXIT_DECISION` row per exit successor
  (a guard with two exit arms twice); its one consumer takes methods. R40
  `ConcolicInstrumentationSelections.InstrumentationPlan.replayAnchorMethods` is redundant with
  `instrumentationMethods`; `isEmpty()`, `STATIC_CONSTANT`/`STATIC_FIELD_UNSUPPORTED`, `matches(…)`
  readers? R41 the skeleton file is read twice by two selection helpers.
- R42 `CausynthPipeline.conservativeDispatchTargets(list)` copies its argument (an identity
  function with a doc). R43 `CampaignEnvelope.writerMethods` is filled and never read. R44
  `originalUnit` falls back to POSITION when no `OriginalUnitIndexTag` is found, after every
  caller has tagged the bodies — a fallback that can only hide a tagging failure. R45
  `instrumentConsumedStaticPrimitiveFieldRead` returns a verdict the caller discards. R46
  `instrumentMethods` swallows any non-named `RuntimeException` from a Soot rewrite with
  `LOG.debug("Skipping")` — symmetric in both passes and invisible; name it. R47 two ignored
  return values (`instrumentLiteMethod`, `instrumentConcolicLoopBounds`). Three gates for
  woven bytecode (the woven-trap rule, `validateWovenBodies`, `VerifyWovenClasses`) are two
  principled ones plus one; fine.

### SMT and EXPLORE

- R49 `Frontier.perTask()` returns `int[2]` per task and only `[1]` is ever set. R50
  `FlipQuery.flippable(corpus, sessionId, decision)` ignores two of its three parameters
  (= `Arms.predicate(term)`). R51 `ClosurePlanner.holds()` "falls back to comparing the ids"
  when `methodsOf(regionId)` is empty — the consumer of R20; with the skeletons required it is
  `methodsOf(regionId).contains(method)` and nothing else.
- R52 public members to grep for readers before keeping: `Corpus.iteration/anyRoot/expressions/
  interactions/declaredSymbols/rootReading/seedSessionIds/waveVerdict/collidingRootSymbols`,
  `SlotTable.opened/stated`, `ObligationFactory.Bounds.defaults`, `Z3.Answer.output`,
  `JsonFields.shallowCopy/textString`, `JavaPrimitiveBoxing.unboxReturn`, the `VmExpressionIr`
  constants and predicates, `MapFields.object/booleanValue/safe`.
- R53 GROW (§10 item 6). `ExploreMain.number` and `ConcolicScheduler.positiveInt` are two
  spellings of one refusal (cosmetic). `Arms`, `FlipQuery`, `ObligationFactory` and `Frontier`
  agree through one key (`ObligationFactory.worldKey`); `ClockMargin` and the `Z3` driver read
  cleanly.

### COMPOSE

- R55 `ComposeMain.symbolicVariableModels` publishes a vestigial row shape (`inputKind=
  CONFIGURED_SOURCE_FIELD`, `sourcePhaseId` = the anchor's render, `fieldSignature` = the domain
  kind's name) that `run_engine.sh`'s `campaign_print_symbolic_variable_models` validates field
  by field: fabricated members on both sides; publish `{rootId, kind, value}`. R56
  `campaignClaim` states `witnessFindings` twice (again under `rootSpace.reportedFindings`) and
  `acceptedFindingKind` = `findingKind`. R57 `VmTermLowering.parseIntTerm` refuses in three
  spellings and can never lower; one refusal. R58 `VmLoweringCore` (911 lines) is an abstract
  layer with exactly one subclass left (`SmtLowering`) and `VmTermLowering.Policy` its
  interface: fold after 9/9. R59 `ContainerSmtCodec.Host`'s default methods are overridden by
  the only host. `Composer`/`ComposedFamilies`/`ClaimPolicy` read consistently with `Arms`; the
  JOIN→PIN→REFUSE rule and "MINT rows first" agree with the CONFIRM change of `a20f56191`.

### Scripts and harness

- R60 `run_engine.sh campaign_plan` copies `schedule.jsonl` *or* `recorded_schedule.jsonl` from
  the trace directory; only the first is ever written. R61 `campaign_static_gaps_json`/
  `campaign_plan_gaps_json` answer `[]` for a missing artifact — require it. R62
  `campaign_write_gaps` labels any other `gaps.jsonl` path REPLAY (`*) gapstage=REPLAY`). R63
  `accept/fatalread.py` reads `z3-result.json` and `guardedReadModel`, which no stage writes, so
  it refuses on every case by construction: delete it and the report's "Fatal read" section, or
  publish the read's arms. R64 `accept/probe.sh acc_root_kind_of` defaults an unlisted case to
  MARKER; the CLOCK branch pins nothing because no stage publishes `recordedRootValues` — the
  probe is reported, never gated, but a signal that can never be computed is noise. R65
  `accept.sh`'s header ("Default: all six"), `report.py` ("the six cases this harness runs") and
  `probe.sh` ("the same six") still count six cases; there are nine. The campaign orchestration
  itself (FREEZE, the wave pool, GROW, CONFIRM, EMIT) reads soundly; `lib/*.sh` and
  `tools/rounds` are declarations plus one launcher, as intended.

### What holds, and what is structurally redundant

The one-place authorities hold and are the reason the design is sound: `Identity.occurrence`/
`endpointAt`, `Arms.pathCondition`/`conjunct`/`predicate`, `RootMint.focusedRootValue`,
`Corpus.rootValue`, `ObligationFactory.worldKey`, `RowRuntime.gap`, `SmtLowering` (one
lowering), `SmtNames` (one tokenizer), `ClaimPolicy` (one claim). The structural redundancies,
in the order they cost: the schedule enforcer's three regimes for one order (D3, fixed first);
three thread-context stacks for one thread (R18); an abstract lowering layer with one
implementation (R58); a runtime-refined graph whose only value over the candidate graph is a
lookup the finalizer already recomputes (R48); recording pass 1 (R13). Everything else in the
list is local.
