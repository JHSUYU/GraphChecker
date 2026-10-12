# docs/design

The design of GraphChecker as the code on this branch implements it. Each document describes
only the present. What is done, partial or missing is in [../STATUS.md](../STATUS.md). The
handover state (branches in flight, rounds, the per-system TODO, the owner's rules, the agent
method, servers and tools) is in [../handover/](../handover/STATE.md). Where a document and the
code disagree, the code is right and the document is fixed.

| document | what it covers |
| --- | --- |
| [PIPELINE.md](PIPELINE.md) | The campaign, stage by stage: SEED, PLAN, INSTRUMENT, REPLAY, IMPORT, EXPLORE, COMPOSE, DECIDE, CONFIRM and EMIT, as `run_engine.sh` and the Java stages run them. |
| [SYMBOL-SCOPE.md](SYMBOL-SCOPE.md) | Which values become symbolic, and why. |
| [IDENTITY.md](IDENTITY.md) | How an event is named the same way in every run. |
| [CONTRACT-SPEC.md](CONTRACT-SPEC.md) | The rows a replay publishes and the rules they obey. |
| [VM.md](VM.md) | The concolic JVM (OpenJDK 8 Zero) under `third_party/OpenJDK-Concolic-Execution-Engine`. |
| [PERFORMANCE.md](PERFORMANCE.md) | Where a campaign's time goes, how ten lifts run many campaigns at once (the ledger, measured charges, the shared pool, head steps), why cases were slow, how to debug a slow case. |

The checks themselves (every point of the four systems, with its live state) are in [../checks/README.md](../checks/README.md).

## The question GraphChecker answers

An *ad hoc coordination* point is a place where one node acts on state that another node or
thread produced, with no protocol that guarantees the two agree. Examples: a DataNode's block
key against the NameNode's rotation; a journal epoch against the writer's; a cached alias
snapshot against the store. The failure site is a guarded `throw` in production code, marked
`throw new @CausynthExceptionTarget("<check id>") E(...)` in the system's tree.

GraphChecker starts from ONE recorded run of the system's own cluster test, in which the throw
does not fire, and explores systematically whether any world around it reaches the throw at the
declared occurrence `(r, c, i)`: it flips the symbolic branches of the throw's slice and the roots
that decide them (flips nest up to 3 deep), replays each flipped world, grows the closure from what
the replays newly reach, and fuses every admitted replay into one formula. The roots are:
- a transport fault at a woven door (either direction);
- a local file-operation fault on the traced flow;
- a clock skew;
- a configuration value;
- a different pairing of a message or of a shared-state read with its writer.

The answer is one formula, `final/candidate.smt2`, composed from symbolic propagation across
nodes. **SAT** means a witness, confirmed by a replay and a native reproduction. **UNSAT** means
no explored world reaches the throw. A run failure is a named RUN_DEFECT: an engine bug, not a
verdict. The owner's reference design is the GreyGraph design §3.1: regions, `(r,c,i)` identity,
writers by concrete location, causal graph extraction, the exploration loop.

## Design at a glance (stage by stage)

**1. SEED: the static slice, the roots and the recording.**

*The slice.* `causynth/SeedBackwardStaticAnalyzer` (Soot) slices backward from the throw's
guards across methods, threads and the wire.
- Library calls follow their contracts: containers, accessors, stateful receivers, clocks, and
  `java.util.stream` with functional arguments.
- Calls and returns are matched (`ReturnOnlyFormals`).
- **Control flow counts as data:** a branch that decides whether slice-carrying code runs makes
  its operands demanded (`SiteControlDependence`, `expandActivationGuards`). This holds inside a
  method, along the call chain and at callers, 3 deep, and stops at execution-context entries.
- An abstract class's concrete methods are in scope.

*Roots, by category only* (`RootCatalog`), never per case:
- CLOCK reads;
- FAULT markers at the library catalog's woven doors (Hadoop IPC, HDFS SASL and DataTransfer,
  SolrJ HTTP, ZooKeeper);
- LOCAL_IO and TIMED_WAIT demanded doors (`DemandedDoors`). These are JDK file operations and
  timed waits (a wait's marker returns its timeout at once), chosen only where a
  failing result reaches the path, or where a latent fault escapes before a demanded store or is
  caught by a handler that decides a demanded site. At most twelve per case. A door's via chain
  folds into the regions holding its site;
- READ placeholders;
- CONFIG keys (`ConfigRoots`; keys at the writers' guards count too);
- tracked shared state: VALUE, IDENTITY and CONTAINER kinds.

*Root demand.* `RootDemand` walks back from the target's path guards to the nearest boundary of
each class (16 edges, 12 per class). Each unchosen boundary is named with why. Scope growth
(`plan/ScopeGrowth`) adds classes within a budget; the IO frontier grows a class only where its
body itself does file IO.

*The recording* runs the workload on stock HotSpot with the woven trace recorder. It records
regions, occurrences and the schedule (`ScheduleLog`: START / CLAIM / SEND / RECV / WAKE). Each
system's cluster adapter opens the window once the cluster is up. A case may opt in to the
startup window.

**2. Identity** ([IDENTITY.md](IDENTITY.md)). An occurrence is (node, region, context, index).
- A context is a Root (a tick, a client step, a WAKE turn), an Anchor (the producer endpoint of
  the message it serves) or Lost.
- The index is the frame path from the root, with per-site invocation counts; a count inside a
  running occurrence is the occurrence's, never restarted by a root hop opened inside it (a tick).
- A planned occurrence is answered by shape: an activation of a planned region on the same node,
  under a chain of the same shape that differs only in counts, takes the earliest unanswered task
  of that shape and its planned address (`Identity#answer`, a DIAGNOSTIC ADDRESS_UNSTABLE names
  where it ran) -- a message the clock decides which heartbeat carries (11741's key update).
- Nodes register through the adapters. Threads are attributed by explicit scope, by registered
  objects on their frames, by inherited source, or by their starter.
- A request's door names its verb (the RPC operation); a transport door's fault ends the request
  in hand, as a receipt does.
- A node startup and a daemon's turn first end the exchange their thread served
  (`MessageDoors#beginTick`).
- Node-startup brackets cover clusters that are built or restarted inside the window.
- A startup step fixes the order in which DataNodes register (the NameNode side of
  `registerDatanode`); every marked startup pass is held, whatever either window's state.
- The declared occurrence must be rooted in the window.

**3. PLAN** (`RuntimeSelectedRegionFinalizer`, `DemandWalk`) plans the closure around the
declared target `(r,c)`: the occurrences that store, or decide against, what the engine moves.
- Static writers are never dropped.
- Equivalent deciders of one demanded store site (same region, context shape, call path and
  recorded events with read versions, no demanded-cell access between them) are planned once per
  class (a polling loop's 1406 turns -> 55 classes, hdfs-adhoc-16).
- Over `schedule_max_jobs`, the recorded writers come first and the rest is cut, named
  `PLAN_CLOSURE_CUT` (BLOCKING).

**4. INSTRUMENT** weaves region hooks, doors (FAULT markers on both directions), the demanded
LOCAL_IO doors, loop bounds, random draws, directory listings (sorted) and timed waits into the case's classes. The result is
checked by the JVM verifier.

**5. REPLAY** runs on the concolic VM ([VM.md](VM.md)).

*Values.* Every value carries a symbolic expression, JVM-level. Containers are modelled as
ASSOCIATIVE/INDEXED chains. A container a field holds is observed by its state (iterators and
views reach their container; an outside mutation marks its log). Shared fields keep version
logs: INITIAL, WRITE, RMW, STATE. Every READ_SITE read publishes a read record stating the
version it observed.

*The schedule.* The recording's prefix is enforced: each event waits for its slot.
- The stall rules release what the run will not make. A watchdog gives up after 15 s, and each
  give-up is logged as "did not happen".
- WAKE turns are never sooner than recorded, nor is a timed-out wait's return: it takes its WAKE
  slot and returns no sooner than its own deadline.
- The scope rules R1–R4 apply (anchors of unstated SENDs, the putter's scope, per-hop start
  frames, giving up own-context slots).
- Random draws are replayed, keyed by the schedule context, the site and a count (stable under
  a GROW). Clock VALUES are not replayed: the time model was reverted (it held a program monitor across a timed-out
  wait's turn); the start-up/clock family runs on workarounds (RULES), and a held timed wait returns no sooner than
  its own deadline (`TimedWaits#outlast`).

*The wire.* A protobuf message field crosses with its message: it is exported at the builder's setter
inside its region, bound to the builder, and handed to the message by its `build()`; the door that
carries the message (IPC request and response, DataTransfer op) walks it and stages each field's
element, or, for a message this JVM decoded, its original producer's; the parse binds each element
to the message object, and a getter attaches the element of the message it reads. A declared row is
exported where the weave captured it. The engine's own plumbing (its runtime classes, generated messages and
builders) is never state ([SYMBOL-SCOPE.md](SYMBOL-SCOPE.md) §5.2, §6.3).

*Read-out.* Read-out pages stream to the publication thread as they are captured.

**6. IMPORT** checks the row invariants and publishes the seed session.

**7. EXPLORE** (`explore/`).
- `ClosurePlanner` builds tasks: a focused occurrence plus its state-connected factor.
- A concrete anchor demands the reads its predicate names, and the reads before its decision on
  the guards' cone.
- Only doors that decided a fault are control producers.
- `ObligationFactory` proposes flips of a task's recorded paths: fault decisions first, at most
  `maxFlipsPerPath` per round, 3 deep.
- `FlipQuery` asks z3 for the nearest world: roots, clock skews, handoff answers, writer choices
  including a location's INITIAL, and the run-as-it-happened arm when reads saw several writes.
- An obligation is a SOLVE (z3 on a host's warm solver) and, only when SAT, a REPLAY that plants
  that world, queued behind the solves; it stays in flight until its replay lands. The replay is judged
  ADMITTED, NOT_ADMITTED (by name), UNSAT or ADMISSION_GAP.
- GROW re-runs extend the closure.
- EXPLORE demands what COMPOSE keeps: the handoffs a fatal condition or a kept writer decision rests on are demanded,
  each resolved straight to its attach row whatever its group, so their producers become tasks (`compose/RestsOn`, one
  admission rule and one closure walk shared by EXPLORE, COMPOSE and CONFIRM).
- A guard on a helper's return is decided by the helper's branch (`ite(decider, the constant arm's verdict, the run's
  own predicate)`, enum constants and `equals` included); an open arm no run took is a flip site of the reached anchor
  and is named at the fixed point (`OPEN_ARM_UNANSWERED`, a RUN_DEFECT when its flips only came back NOT_ADMITTED);
  a replay that ran the arm's world faithfully and never entered its occurrence refutes that world (`WORLD_REFUTED`),
  and the flip is asked again without it. A path that asked its own flip of the arm is judged by that flip (task,
  path, decision, outcome) over every answer it got, whatever obligation id each ran under, a refuted world answering
  nothing; one that never asked shares the answer of the arm its id names (`ExploreMain#openArmState`);
  a replay that did not run its world faithfully (`WORLD_UNREFUTED`) is asked once more and named on the arm's row
  (`unrunWorlds`).
- An integral configuration's domain also takes every literal a recorded decision compares it with, within what its
  own validation admits (`contract.Validity`), through one reader (`explore.Corpus#domainOf`).
- The campaign's queue by kind (`campaign_stream_enqueue`): a witness CONFIRM and GROW's re-runs first, then the
  solves, then the REPLAYs (newest first): a solve takes seconds and decides whether a replay is owed (solr-adhoc-21
  RX4: 1075 of 1158 obligations in flight were solves never started behind replays). Dispatch starts the first entry a
  host admits; an entry queued past `campaign_stream_wait_bound_s` (600 s) goes first and alone, so no replay starves.
- A declared bound that cut the search (wave budget, paths per task round, world depth, task bound, PLAN's closure
  cut, the claim bound) is named in `result.json` `bounded`.
- The first replay that observes the fatal at the declared occurrence ends the exploration: the
  first witness.

**8. COMPOSE / DECIDE** (`compose/`).
- One formula covers every admitted session. Each message and each shared-state read gets a
  family of writer arms (exactly one is chosen), each guarded by the path condition that produced
  it. Eligibility is one rule (`Arms#eligible`).
- Every clock cell is placed on the recording's timeline before any path composes (`Composer#placeClocks`, every seed
  reading an anchor); a cell no session can place refuses only the paths that name it.
- What is symbolic stays symbolic. A value whose stated producer moves (by `movers()`, the one
  predicate) is a FREE leaf; a value no row states the producer of is HELD at its recorded value,
  named in `concrete[]` ("producer unstated"); a container state the VM marked incomplete is
  refused (an unhooked mutation came between). Every refused path is listed (`refusedPaths`).
- The run as recorded is always a world of the formula (a writer whose block the run broke gets
  the observed arm); a path contradicting its own run is PATH_SELF_CONTRADICTORY.
- WIRE pairing: by the VM handle, else by (correlation, half, port) of the very message the element
  arrived in (a message field's: the message object its getter is called on, which the door's walk
  bound it to); an element a message did not carry pairs with nothing and is named.
- `candidate.smt2` is the full formula: the disjunction of admitted paths, roots free over their
  domains, the fatal arm asserted. The verdict is z3 on exactly that file.
- The claims:
  - **SAT_CANDIDATE**, with finding kind MARKER_FLIPPED, CLOCK_SKEW, STATE_/MESSAGE_PAIRING_FLIPPED
    or FORMULA_SAT, and `polarityDecides`.
  - **UNSAT_CLOSED**.
  - **RUN_DEFECT** (a solver timeout, CONFIRM with no verdict, a target never reached, an
    exploration cut while it owed arms: EXPLORATION_CUT, judged once at EMIT).
- A model CONFIRM refuted (a false positive) excludes the claim's region (its clocks' too) from every
  later composition; an UNSAT whose unsat core names a refutation states `restsOnRefutations`. Within a rank, a witness that is its selected session's own run
  is claimed first; each valuation is asked once across both rank passes.

**9. CONFIRM** replays the witness world from the recording. It holds the chosen edges (writer
ORDER, STATE pairings including INITIAL, WIRE deliveries) and checks that the anchor observes the
fatal. It is strict: every substitution is named. A replay that does not reach the fatal at the
anchor -- no fatal, a CONFIRM_MISMATCH, an ORDER not held in time, a plant not applied, a stall, a
timeout -- refutes the claim, a false positive (owner 2026-10-08), excluded from later compositions
so the next claim follows; a task refused by name or a failed decision is the engine's defect, and
a final claim left so is a RUN_DEFECT. In a campaign it is a pool job on any host. The witness is
chosen by attempt order, not finish time.

**10. EMIT / REPRODUCE** write `candidate.smt2`, `claim.json`, `confirm.json` and `result.json`
(with `concrete[]`). Native runs then plant the confirmed world (fault markers, hook roots, clocks,
configurations, accessor reads, call-return answers, the model's order; PIPELINE §10b). Acceptance is
`experiments/accept/report.py` plus `cone.py` (the moved roots lie in the witness cone, and no
fatal boundary variable is unbound).

**11. The campaign driver** (`run_engine.sh`).
- One head per case. Heavy steps go wherever the host ledger has room (at most 70% of a lift's
  memory, with leased charges); a head holds its measured step need.
- Replays are charged the campaign's measured need. Obligations stream over every lift; a sweep's
  cases share one pool. Details and pitfalls: [PERFORMANCE.md](PERFORMANCE.md).
- The budget's reserve covers COMPOSE, EMIT, CONFIRM and REPRODUCE.
- The host ledger's memory reading is refreshed by one shell per host (`<host>/refresh`); the others use a reading up
  to 30 s old.
- In the body since the 10-06 handover: every static export site woven and a witness's own chain closed before it is
  claimed, the IPC hand-off naming (r6/r7 trees), the owed-path bound, codec capture, open arms (`WORLD_REFUTED`,
  configuration domains), the wait deadline and the open-arm keys (STATE §0). Parked: confirm-first, the loop prefix
  as its own occurrence, the reply consumer by request ordinal (TODO HDFS §2-§5).
- WIRE-CODEC (codec holes in opaque payloads) is not in the body: branch `wire-codec-p1`.
