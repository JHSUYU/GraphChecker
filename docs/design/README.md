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
- LOCAL_IO demanded doors (`DemandedDoors`). These are JDK file operations, chosen only where a
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
- The index is the frame path from the root, with per-site invocation counts.
- Nodes register through the adapters. Threads are attributed by explicit scope, by registered
  objects on their frames, by inherited source, or by their starter.
- A request's door names its verb (the RPC operation).
- Node-startup brackets cover clusters that are built or restarted inside the window.
- A startup step fixes the order in which DataNodes register (the NameNode side of
  `registerDatanode`).
- The declared occurrence must be rooted in the window.

**3. PLAN** (`RuntimeSelectedRegionFinalizer`, `DemandWalk`) plans the closure around the
declared target `(r,c)`: the occurrences that store, or decide against, what the engine moves.
- Static writers are never dropped.
- Over `schedule_max_jobs`, the recorded writers come first and the rest is cut, named
  `PLAN_CLOSURE_CUT`.

**4. INSTRUMENT** weaves region hooks, doors (FAULT markers on both directions), the demanded
LOCAL_IO doors, loop bounds, random draws and timed waits into the case's classes. The result is
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
- WAKE turns are never sooner than recorded. An empty turn holds no slot (T1).
- The scope rules R1–R4 apply (anchors of unstated SENDs, the putter's scope, per-hop start
  frames, giving up own-context slots).
- Recorded random draws are replayed.

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
- A SAT model becomes an obligation replay that plants that world. The replay is judged
  ADMITTED, NOT_ADMITTED (by name), UNSAT or ADMISSION_GAP.
- GROW re-runs extend the closure.
- The first replay that observes the fatal at the declared occurrence ends the exploration: the
  first witness.

**8. COMPOSE / DECIDE** (`compose/`).
- One formula covers every admitted session. Each message and each shared-state read gets a
  family of writer arms (exactly one is chosen), each guarded by the path condition that produced
  it. Eligibility is one rule (`Arms#eligible`).
- What is symbolic stays symbolic. A value that moves with a root is a FREE leaf. A value nothing
  moves is a constant, listed in `concrete[]` with what it moves with.
- `candidate.smt2` is the full formula: the disjunction of admitted paths, roots free over their
  domains, the fatal arm asserted. The verdict is z3 on exactly that file.
- The claims:
  - **SAT_CANDIDATE**, with finding kind MARKER_FLIPPED, CLOCK_SKEW, STATE_/MESSAGE_PAIRING_FLIPPED
    or FORMULA_SAT, and `polarityDecides`.
  - **UNSAT_CLOSED**.
  - **RUN_DEFECT** (a solver timeout, CONFIRM with no verdict, a target never reached).
- A CONFIRM refutation excludes the claim's clock region from every later composition.

**9. CONFIRM** replays the witness world from the recording. It holds the chosen edges (writer
ORDER, STATE pairings including INITIAL, WIRE deliveries) and checks that the anchor observes the
fatal. It is strict: every substitution is named. In a campaign it is a pool job on any host. The
witness is chosen by attempt order, not finish time.

**10. EMIT / REPRODUCE** write `candidate.smt2`, `claim.json`, `confirm.json` and `result.json`
(with `concrete[]`). Native runs then plant the fault markers. Acceptance is
`experiments/accept/report.py` plus `cone.py` (the moved roots lie in the witness cone, and no
fatal boundary variable is unbound).

**11. The campaign driver** (`run_engine.sh`).
- One head per case. Heavy steps go wherever the host ledger has room (at most 70% of a lift's
  memory, with leased charges).
- Obligations stream over every lift. A sweep caps each case's share.
- The budget's reserve covers COMPOSE, EMIT, CONFIRM and REPRODUCE.
