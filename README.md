# GraphChecker

## 1. What GraphChecker answers

You have a distributed Java system, a failure that some configuration, clock or message
ordering can cause, and one recorded run of a workload that does **not** fail. You annotate
the exception construction that is the failure, name the occurrence of it the case is about,
and declare a handful of inputs: which cells are roots (fault markers, configured sources,
clock reads), which message fields cross which boundary, and a bound for each retained loop.
GraphChecker then explores single counterfactual decisions around that run and publishes two
artifacts: `candidate.smt2`, a quantifier-free SMT query whose satisfying valuation *is* the
condition under which the annotated site fails, and `claim.json`, stating the finding kind,
which declared roots the witness had to move, and whether the polarity decides — whether the
same formula refutes the run as it happened. There is no confirmation replay: the composed
query and z3's verdicts on it are the deliverable, and anything the recording does not state
is refused by name rather than defaulted.

## 2. The core idea

Six commitments; the rest of the system is derivable from them.

**Roots are declared, not discovered.** A symbol enters at exactly three kinds of place, all
named by the case: a *root* mint (a fault marker, a configured source, a clock read), a
*declared region input* (a read of a cell the case names, minting a placeholder for the value
read), and a *wire attach* (an inbound leaf, minting a handoff `v_H` paired with the producer's
export). Everything else stays concrete until a symbolic value is *written* into it.

**Values propagate inside the JVM; the static graph only scopes.** Replays run on a
customized OpenJDK 8 Zero interpreter that keeps a shadow expression under each value — by
value, under the real object identity, not by a declared location — so a read returns the
expression written there, through fields, containers, threads and across the wire. The fatal
read's value in every replay is therefore already an expression over the declared roots. The
static slice has one job: which regions are instrumented, and which write and export sites of
a demanded location are observed. It never finds a writer, reconstructs a value's provenance,
or stitches an input to an output. The Java-side view of that VM — the broker ABI, what each
capability buys, and what it refuses — is [docs/CONCOLIC_INTEGRATION.md](docs/CONCOLIC_INTEGRATION.md).

**One structural identity, computed the same way in both passes.** An occurrence is addressed
by where it is in the program and why it ran, never by a thread id, address or per-run counter,
and both passes feed that function the same inputs (§4), so sameness is decided by equality.

**The replay unit is one decision flip on one occurrence.** A focused replay makes exactly one
occurrence symbolic (or one state-connected factor: the writers and readers of one location on
one node) and asks it to take the other arm of one decision at one site and ordinal; all else
runs concretely, exports recorded and attaches minting handoffs. Such a replay *collects an arm
the recording lacks*; it confirms nothing.

**Edges are joined in the SMT, not by execution.** No replay realizes a cross-node chain end
to end. Each publishes its own path condition and expressions; the composer merges them into
one disjunction, and a message or shared-state edge becomes a *family* of arms over the handoff
variable the consumer minted. Two flips on two nodes are recorded separately and joined, never
scheduled together.

**Fail closed, by name.** Every refusal is a gap row of a closed kind (`contract/GapKind.java`
is the whole registry), classed `BLOCKING` (the stage fails, naming the row, field and owner)
or `DIAGNOSTIC` (recorded, the campaign goes on). No cap, default, heuristic match or
synthesized value anywhere.

### Why not the simpler designs

*Symbolic propagation alone.* The recording is, by nature, the healthy run. When a root
reaches the target only through **control dependence** — a store the healthy arm skips — the
fatal predicate on the recorded path is a literal, and no formula over the recording alone is
satisfiable at a flipped root; HDFS-17960 is exactly this shape. Conversely, exploring *without*
in-JVM propagation means rebuilding provenance offline from the graph: the stitching to avoid.

*Linked replay.* An earlier design made a primary occurrence and its companions symbolic in
one run. Two costs follow: admission couples unrelated regions (a loop-prefix mismatch on the
NameNode side rejected an otherwise good DataNode primary), and replays grow as the *product*
of the regions' local path counts. Focused replays cost the *sum*, admission is decided from
the focused region's own rows, and the edge is joined afterwards by the family instead.

*Exhaustive flipping.* HDFS-17960's seed session publishes 1,113 decision rows; flipping them
is not a search strategy. Demand starts at the annotated site — the operands of the fatal
predicate and the branch sites the target is control-dependent on — and the closure grows only
along boundary inputs of demanded values. Wave 0 proposes **4** obligations, wave 1 is a fixed
point. HDFS-11741, two nodes and 86 planned tasks, proposes **36** in wave 0 and reaches a
fixed point in the next wave. An obligation's identity is `(task, site, ordinal, flipped
outcome)` and it is owed **once across the corpus** (`explore/Frontier`); before that rule the
same handful of flips was re-proposed hundreds of times in one wave.

## 3. The pipeline

One campaign per case, driven by `run_engine.sh`. Inputs are frozen before any work, and each
iteration (topology **epoch**) writes its own immutable directory and composes its own answer.

| Stage | Consumes | Produces | Gate |
| --- | --- | --- | --- |
| `PREFLIGHT`, `FREEZE_TOOL`, `SETUP`, `FREEZE` | workflow config, jar, workload tree | frozen inputs, reserved campaign root | an unknown workflow config key, or a campaign root already holding a published run, is refused by name |
| `SEED` | workload command, stock JDK 8 | the static slice (`static_scope_map.jsonl`, the candidate graph and candidate region skeletons) and **two recording passes** (below) | recording opens only after the workload registers its stable node sources; each pass must publish its own artifacts or the campaign refuses by name |
| `PLAN` | both passes' artifacts, the static scope map, the declarations | `execution_task_plan.jsonl`, the declared target resolved to a full address | a declared input whose method no planned region covers is refused; one plan row per planned occurrence |
| `INSTRUMENT` | selected skeletons, static scope map | instrumented classes | every woven body is validated, then JVM-verified fail-closed |
| `REPLAY` (seed) | instrumented classes, custom VM | the seed **session**: one file per row kind plus its expression table | frame pushes and pops pair one-for-one (`FRAME_UNBALANCED`) |
| `IMPORT` | the epoch's sessions, and again every wave's new ones | gap rows | the row contract, checked here and nowhere else (§5); `BLOCKING` fails the campaign at that wave |
| `EXPLORE` | every session so far, static scope map, root domains | per wave: `obligations.jsonl`, one focused session per obligation, `obligation_results.jsonl` | an unbound symbol in a flip model is `UNPRODUCIBLE_ANSWER`, never sat; a solver error is `NOT_ADMITTED`, never unsat; an arm a session already recorded is not re-flipped |
| `COMPOSE` | the corpus, families, root domains | `candidate.smt2`, `candidate_composition_manifest.json` | a read that joins no version and pins no value is `UNSTATED_VALUE` and refuses |
| `SOLVE`, `DECIDE` | the composed query | a z3 answer per valuation, `claim.json` | satisfiable at the recorded valuation on a healthy recording is a blocking alarm; a witness moving a root inside an unattested arm is refused |
| `EMIT` | all of the above | `result.json`, `gaps.json`, `run-manifest.json` | the final set must hold `candidate.smt2`, `candidate_composition_manifest.json`, `gaps.json` and `result.json`, with `claim.json` beside them; acceptance is the claim **and** the named gaps together |

**`SEED` records twice, and the second pass is scoped by the first.** Pass 1 weaves *lite*
hooks — method activation envelopes only — over every **candidate** region, runs the workload,
and aggregates its trace (`runtime/CausynthTraceRecorder --region-skeleton-only`) into the
regions that actually ran: `skeleton-pass/region_skeletons.jsonl`, the runtime-selected set,
beside `skeleton-pass/recording_gaps.jsonl`, the gaps that pass stated. Pass 2 re-weaves *rich*
hooks over only those regions (`CAUSYNTH_TRACE_MODE=region-state`), re-runs the same workload,
and records identity frames, decisions, call-site and argument captures and the exchanges; its
aggregation publishes `concolic_region_plan.jsonl` and files pass 1's gaps with its own, since
the recording has no session to hold a gap row. `PLAN` reads both. Folding the two into one is
what the split buys: one pass weaves 486 and 58 methods where two weave 198 and 43.
The refined-graph builder (`runtime/RuntimeRefinedGraphBuilder`) and the field-trace hook
still exist at this commit; their deletion is the PC4 to-do below.

`EXPLORE` runs in waves: one JVM plans the wave — reading every session the epoch has produced
and writing the obligations the frontier is owed — and one worker per obligation runs a focused
replay. `IMPORT` runs again on each wave's own new sessions (`campaign_import_wave_gate`), not
just on the seed: a wave is where a focused session is made, so it is where the row contract is
checked, and a `BLOCKING` violation fails the campaign at that wave by name. Two refusals keep
the solver and the replays for questions the corpus lacks an answer to, both `ADMISSION_GAP`
rows of the **wave** and `DIAGNOSTIC`, because they state a fact about the question this wave
asked and about no execution. A flip query that declares no variable of its own — no root, no
clock, no handoff control, no movable read reaches the flipped predicate — is refused in
`explore/FlipQuery` before z3 sees it: whichever arm it takes, the answer is the recording's own
facts. A model that hands every root back the value the recording minted and answers no handoff
is refused in `explore/ObligationFactory` before a replay is spent: that world is the seed
replay under another name.

The closure it walks is `explore/ClosurePlanner`, recomputed from scratch each wave: demand
starts at the annotated target — the operands of the fatal predicate as the VM states them, and
the guard set of the target site — and each boundary variable of a demanded value grows it both
by the **rows** (the producer that paired with an attach, the writers whose versions a read
could have observed) and by the **static map** (every occurrence of a region holding a write
site of that location, or an export site of that port), because on 17960 no row of any session
puts the deletion region in the anchor's closure and a closure that waits for one waits for the
replay it is supposed to ask for. Both stops are coverage telemetry, never a failure: a wave
proposing the same obligations with the same verdicts has learned nothing
(`REGION_PATH_CLOSURE_NO_PROGRESS`), and an unexplored sibling blocks a closed `UNSAT` while
saying nothing about a satisfiable witness. A replay pairing an endpoint this epoch's catalog
lacks is a `TOPOLOGY_DIVERGENCE`: the *next* epoch is planned from that replay's own trace.

That closure is not the static graph's region selection, which is `PLAN`'s own and runs first.
`causynth/RuntimeSelectedRegionFinalizer` prunes the recorded regions failure-directed, back
from the target through the retained flows (104 → 28 regions on 17960, 26 → 15 on 11741), and
publishes on each surviving plan row the `admissionBasis` saying why it is there at all:
`SHARED_LOCATION_DEMAND_V1` for a demanded state writer (with its `demandDepth`),
`DECLARED_SYMBOLIC_INPUT_V1` for a region whose root method the case declared symbolic, and
`DECLARED_COMMUNICATION_CAPTURE_V1` for one that performed a declared capture — admission *by
declaration*, because nothing on this node demands an export's outputs and an export outside
every instrumented activation has no decision prefix, which is how HDFS-11741 published all 13
arms of its key-id family unattested.

The Java side is organized by those notions:

| Package | Holds |
| --- | --- |
| `contract` | the row kinds, the identity types (`OccurrenceAddress`, `CausalContext`, `ExecutionIndex`, `LocationId`), `GapKind`/`GapClass`, and the `IMPORT` gate |
| `causynth` | the Soot pass: static slice, weaving and its verification, failure-directed region scoping, and the aggregation of both recording passes |
| `plan` | what the scoped program is planned as: `StaticScopeMap`, `ExecutionTask`, the scheduler, declared inputs, loop-bound policy |
| `runtime` | the recording and replay hooks, the frame journal, row publication, focused replay, the VM broker |
| `explore` | the closure, the frontier of owed arms, flip queries, obligations and waves |
| `compose` | the disjuncts, the SMT lowering, the container model and the claim policy |
| `smt` | the expression IR, arms and families, canonical JSON, and the z3 driver |
| `annotation` | the target marker `@CausynthExceptionTarget`, and `Debug` for a workload-planted one |
| `option`, `transformer` | the Soot pass's command line, and the one `SceneTransformer` that registers it |

## 4. Identity

An occurrence's address is structural, and it is the same function of the same inputs in the
recording pass and in every replay:

```
OccurrenceAddress = node#epochN            logical component and topology epoch
                  / region/REGION.<id>     static region (code)
                  / ctx:<CausalContext>    why this occurrence ran
                  / idx:<frame>/<frame>/…  where in the component's control structure
```

`CausalContext` has three forms and no others. `Anchor(producerEndpointId, rpcSite)` — a
message started it, and the anchor is the producer's endpoint id, recursively carrying the
producer's own context. `Root(role/api, k)` — a workload action or daemon tick with no incoming
message, the k-th such root of that role and api in the recording window. `Lost(role)` — the
scope was unattributable: degraded, and still an identity, not a guess.

The execution index is PEPID-shaped (Execution Indexing, PLDI 2008; Precise Execution Point
IDs, ASE 2013): the frames from the scope root to the region entry, each a static call site
with the iteration count of its innermost enclosing loop, so an unrelated extra call elsewhere
does not move it. An **endpoint** — what a message pairing, a read or a write is addressed by —
is `(occurrence, site, site-local execution index, attempt)`, that index being the same frame
form from the region entry to the site.

**A state location's owner is the VM's own object identity, not an allocation site.** The
runtime spells one location one way on both sides of a join — `RowPublication`'s
`KIND/<ownerSymRid>#<slot>`: `INSTANCE_FIELD/1#24`, `STATIC_FIELD/…`, `ARRAY_ELEMENT/…`,
`MAP_STATE/<rid>#-3` for a whole container — where the owner is the symbolic rid the VM gave
that object and the slot is the field offset, the index, or the reserved whole-state slot.
`contract/LocationId` carries it as `(kind, owner, slot)`, and `smt/Arms.namedOwner` is the one
place that asks whether an owner names its storage well enough to offer a read *alternative*
writers: a numeric rid does, and so does `STATIC`, because a class owns exactly one cell.
A rid is a **per-run counter**, so a state join is per **session** — the write log and the read
rows of one run, spelled the same way on both sides — and inside that run it names exactly one
object; `Arms.stateArms` takes its writers from that session and no other. The
allocation-endpoint owner this used to mint (Memory Indexing, FSE 2010) is deleted: no main
code produced it, and the gate that admitted only it refused every row of both corpora.
Cross-replay object identity comes back when a producer needs it.

**The pass-equality rule.** The identity is one function *and one input set* in both passes:
node attribution, the region frame set (every skeleton root opens a frame in both passes; rich
and lite hooks never both on one method), thread-start frames claimed at the work's first
identity event, an index frame at every application-scope method, loop frames and any
loop-iteration charge, the producer endpoint and read/write site indexes. Any new hook that
pushes a frame or counts an event is woven in both passes or in neither, every push paired with
its pop, because the address *is* the join key — which plan row a replay answered, which arm a
family owes, which version a read observed are all equality on these ids.

What the identity deliberately does **not** tolerate: a different *number* of iterations of a
loop on the index path (iteration k aligns with iteration k, so one extra iteration shifts every
later address, and the campaign refuses the affected tasks by name rather than matching
heuristically), and work started inside unwoven JDK internals, which degrades to `Lost`.

## 5. Rows, and the composition

A replay publishes one row per event, one file per kind, into its own session directory, with a
manifest stating its role (`SEED` or `FOCUSED`); every reference resolves in its own table.

| Row | States |
| --- | --- |
| `ActivationRow` | an occurrence ran: address, whether focused, whether instrumented |
| `DecisionRow` | a branch: site, ordinal, the jump's predicate as written at the site (polarity-free), and `outcome` — whether it held |
| `RootMintRow` | a declared root minted here: kind (`MARKER`, `INTEGRAL`, `CLOCK`), recorded value, resolved domain |
| `ReadRow` | a read: location, the version it observed, or the placeholder it minted, or its concrete value |
| `WriteRow` | a write: location, version, the expression written, the writing occurrence |
| `ExportRow` / `AttachRow` | a message leaf left / arrived: endpoint, expression or minted `v_H`, the paired producer |
| `TargetRow` | the annotated site: the fatal predicate in the **fatal** polarity, whether that arm was observed, whether the anchor was reached |
| `GapRow` | a refusal or a diagnostic: kind, class, subject, detail |

`IMPORT` checks ten invariants over the sessions handed to it and nowhere else, because a bad
row is not one stage's problem: a session states its role; one activation row per activation and
one row per event; a read has an observed version or a concrete value, never neither, and joins
the expression of that version or of the placeholder it minted, while no write fabricates a
value; one symbol spelling and one sort per name, every reference resolving in its own session;
`outcome` says whether the published term held; a root mint exists only for a declared root; the
target's term is in the fatal polarity; a flip is admitted only if it took the other arm.

The composer aligns, merges, lowers and gates. For anchor `A` over admitted paths `p`:

```
exactly-one(selector_p)                                   ; target_path_partition
or(selector_p)                                            ; fatal_target
selector_p => pi_p /\ phi_p /\ reads_p /\ joins_p /\ valuation_p
selector_p => family(I)    for every interaction I that p's chain reaches
root domains, clock floors, opaque-identity axioms
```

`pi_p` is the path's decision prefix **strictly before the target observation** — each conjunct
`outcome ? term : not term`, taken with `seq` below the target row's own. That bound is what
makes the conjunction a question rather than a contradiction: the anchor's decision and the
target row share a seq, so a prefix over *all* of the occurrence's decisions carries the
anchor's recorded polarity while `phi_p`, the fatal predicate as published, asserts its
complement, and every path whose session did not observe the fatal arm is unsat before any root
is considered. `pi_p` is then closed over the **writer and producer occurrences this path's
joins reach** (`Composer.closure`, a row-level fixed point), each one's prefix taken strictly
before the write that reached it: a read bound to the expression of a write version is bound to
a value that occurrence *produced*, under the decisions it had taken by then. Those prefixes are
per session, already under this path's valuation, and they are where every clock conjunct lives
— without them 11741 declared no clock symbol and `CLOCK_SKEW` was unreachable.

`reads_p` joins each read to the expression of the version it observed, or to the placeholder it
minted, or pins it to the recorded value — refusing if it can do none of the three. `joins_p`
carries the boundary variables: minted root symbols, container states `v_C` (a container
crossing occurrences becomes a state variable at its first symbolic write, every later operation
a version), wire handoffs `v_H`, per-session clock readings. `valuation_p` is what *this* path's
replay ran each varied root at: never a global fact, because one session's value asserted for
all paths closes every other. Clocks are stated **one floor per cell**, never per (cell,
session): a mint's symbol names the (root, occurrence) and is the same in every session that
read it, so a floor per session states one `:named` assertion many times and z3 answers the
whole query with an error. The reading that floor is relative to is the **seed's** — there is no
corpus-wide "the reading", and a claim about the recording rests on the recording's.

A family arm is `(producer path condition, delivered expression)`, guarded by the delivering
replay's valuation of only the roots that expression depends on. **An arm is attested when the
producer occurrence's rows are stated** — an activation row for it, instrumented, so its
decisions are recorded — in whichever session states them, because attestation is a property of
the producer's run and not of the consumer's. An arm no session attests is `UNATTESTED_ARM`: it
says what was delivered and not why, and a witness moving a root inside one is refused. `v_H` is
bound to what an obligation answered it, else to the delivery an attested arm states, else to
nothing: the third rule, which pinned the arrival to the literal this session happened to
receive, is deleted, because an arrival is not a statement about why the delivery was that value
— so a read no attested arm delivers is refused by name and its path leaves the disjunction.
A wire arrival is bound by its family and by nothing else, and a family's selector is a
**(producer occurrence, session)** and not an arm (rule 3 of §9). One selector per (P, S) binds
ALL of P's outs at once — `sel_{P,S} ⇒ π_{P,S} ∧ guard_{P,S} ∧ closure_{P,S} ∧ ⋀_k v_H_k = e_{k,S}`
— and exactly one of the ELIGIBLE sessions of P holds; S is eligible only where it has an
attested delivery at *every* interaction the path binds of P, so a run that exported four entries
is no option for a path that attached five, and a producer no session is eligible for refuses the
path by name (`UNPRODUCIBLE_ANSWER`). An arm is then closed like a path: P's prefix taken to the
LAST delivery the path takes from it, the same row-level closure the anchor gets started at P,
the container versions the delivered expressions read, the prefixes and state joins of everything
that closure reached, and P's own attaches as nested families under the same selector — never the
anchor's. A refusal inside one refuses that (P, S) and not the path. The manifest names the
(P, S) each witness valuation selected (`selectedArms`); a path states only the joins its
conjunction reaches. State families take the same rule with the WRITER as P: one selector per
writer occurrence, and one exactly-one per location over its writers, because a writer's writes
move as a block and half a block cannot move.

Root domains are exactly what the case declares: a marker free in {recorded, flipped}, an
integral root in its declared relative window, a clock with a floor of zero and no window, any
other root pinned to its recording.

`DECIDE` asks each composed path, alone and with every root free, whether it is satisfiable at
all. One that is not is inert and is named `PATH_SELF_CONTRADICTORY`, `DIAGNOSTIC` per path,
because that may be a fact about the corpus rather than a defect. When **every** path is inert
the same kind is raised `BLOCKING`: the disjunction is false in every world of the corpus, so
its verdicts are about the formula it built and not about the recording. `polarityDecides` is a
condition on the claim, not a field beside it: the recorded valuation's disjunct must be unsat
**and** its unsat core must name a valuation pin, because "the run as it happened does not reach
the fatal arm" is a statement about the recorded roots, and a core naming none refuted the
path's own conjunction under every valuation there is.

The claim policy names the *narrowest* mechanism the evidence supports, and publishes it only
if the polarity decides — the disjunct for the run as it happened must be unsat, or the formula
was satisfiable all along and explains nothing:

| Claim | What it means |
| --- | --- |
| `MARKER_FLIPPED` | a declared root moved inside its declared domain reaches the fatal arm |
| `CLOCK_SKEW` | nothing declared moved; the fatal arm is reached only because clock cells may sit elsewhere, and pinning every cell to what its session read is unsat. The cells the model placed are the witness's moved roots |
| `MESSAGE_PAIRING_FLIPPED` / `STATE_PAIRING_FLIPPED` | every root stays at its recorded value; a different eligible, attested producer or writer delivers the read |
| `RECORDED_FAILURE_EXPLAINED` | the recording itself observed the fatal arm, reproduced with nothing moved |
| `NO_SUPPORTED_WITNESS` | nothing in the corpus supports a witness. An answer, not an error |

## 6. Preparing and running a case

You need stock JDK 8 and Maven for GraphChecker and the recording passes, the customized
OpenJDK 8 Zero VM for concolic replay (build and smoke-test details in
[third_party/OpenJDK-Concolic-Execution-Engine/README.md](third_party/OpenJDK-Concolic-Execution-Engine/README.md)),
z3, `jq`, `python3`, and the workload's compiled classes and complete classpath. Each Hadoop
workload has its own checkout so its source changes and compiled classes stay independent, and
`experiments/hadoop/<case>/run.sh build` installs the current GraphChecker API, compiles that
tree with Java 8 and runs its concrete workload test, refusing unless that one test passes
alone.

```bash
export JAVA_HOME=/absolute/path/to/jdk8 && export PATH="$JAVA_HOME/bin:$PATH"
mvn -q -DskipTests package
JOBS=4 third_party/OpenJDK-Concolic-Execution-Engine/scripts/causynth_build_in_docker.sh
```

| Declaration | Where | What it says |
| --- | --- | --- |
| the failure | `@CausynthExceptionTarget` on the constructed exception type, plus `target.yaml` | which exception construction is the failure |
| the occurrence | `declared_target_occurrence` | which occurrence of that site this case is about, as a full address — a campaign is target-directed, and the case knows which instance can fail |
| roots and region inputs | `symbolic-inputs.jsonl` | a cell whose read mints a placeholder, or a callee-level clock declaration (`<org.apache.hadoop.util.Timer: long now()>` with `"kind": "CLOCK"`) making *every* call site of that clock a `ROOT_SITE` of the scope map, and so a root |
| root domains | `root-domains.jsonl` | per root, an absolute or relative window (`+0`/`+3`) and why. A root with no row stays pinned to its recording, which is what a case that claims nothing about it says |
| message boundaries | `communication-mappings.jsonl` | one `WIRE_FLOW` per typed producer/consumer pair, each side with a capture kind (`METHOD_PARAMETER`, `METHOD_RETURN`, `CALL_ARGUMENT`, `CALL_RETURN`) |
| loop bounds | `loop-bounds.jsonl` and `causynth_loop_default_bound` | the exact bound of each retained condition-controlled loop, with a reason. A campaign stating no default is refused; every inherited bound is published as a diagnostic gap |

The workload also carries a small tracing ABI — **24** entry points across
`runtime.CausynthTraceRecorder` (16), `runtime.ConcolicRegionRuntime` (4),
`runtime.SymbolicMessageEnvelope` (3) and `annotation.Debug` (1): register a node source and its
aliases, open and close a request or daemon tick, carry a scope across a thread hand-off, take
and install a message envelope, symbolize a configured source, plant a marker. Called by name
from the workload trees against an installed jar, they are woven nowhere and a `git grep` of
`src/` finds none of them, so they are pinned as a checked test resource,
`src/test/resources/external-callers.txt` (`ConcolicHookAbiTest`).

**Pinning nondeterminism is part of case preparation.** Before recording, disable or pin the
daemons and timers that write state inside the instrumented window (edit-log autoroll, lease
and resource monitors, heartbeat and key-update periods), make restarts and checkpoints
explicit and awaited, and remove RPC retries across restarts; a replay running a different
*number* of iterations is refused by design (§4).

```bash
./run_engine.sh --config /absolute/path/workflow.properties config    # normalized config
./run_engine.sh --config /absolute/path/workflow.properties validate  # required fields
experiments/hadoop/hdfs-17960/run.sh campaign                         # the whole campaign
CAUSYNTH_CAMPAIGN_STOP_AFTER=IMPORT experiments/hadoop/hdfs-17960/run.sh campaign
```

Use a fresh `CAUSYNTH_OUTPUT_DIR` per campaign and leave its inputs alone until it finishes.
`campaign_stop_after=IMPORT` returns right after the gate with the seed session and its row
census — what a change to the recording or replay path is gated on — in a fraction of the time.

The epoch's answer is under `schedule/final`: `candidate.smt2`, its composition manifest,
`claim.json`, `result.json`, `gaps.json`, the frozen provenance. Read them together — a
`claim.json` naming a mechanism is not acceptance on its own; acceptance is the claim **plus**
`polarityDecides`, no blocking gaps and fresh provenance — and read the gap rows with their
`cls`: `DIAGNOSTIC` describes coverage the run lacked, `BLOCKING` is why it refused.

The in-tree acceptance harness is `experiments/hadoop/accept/` — `accept.sh`, `probe.sh`,
`report.py`, and its own [README](experiments/hadoop/accept/README.md). `accept.sh` builds the
jar, then per case runs that case's `run.sh validate` and `run.sh campaign` into a fresh output
directory, one case at a time; `CAUSYNTH_CUSTOM_JDK_HOME` has no default and an unset one is
refused by name. `report.py` passes a case only when `claim` is `SAT_CANDIDATE`, `finalStatus`
is `FINAL_READY`, `blockers` is empty with no open `BLOCKING` gap, `polarityDecides` is true,
`valuationOrdinal` is at least 1 with a non-empty `movedRoots`, and `findingKind` is the
mechanism that case is known to fail by — the `EXPECTED_MECHANISM` table at the top of
`report.py`, which is also why a case the table does not name cannot pass. `probe.sh` is
reported and never gated on: it asks the published `candidate.smt2` plain, then at the accepted
assignment and at the other polarity, **unpinned**. That last word is the point, because a plain
`z3 candidate.smt2` answers `unsat` on a passing case and that is no verdict about it: the
composer writes its own recorded valuation into the file it publishes,
`(assert (! (= <root> …) :named valuation__…))` under `; valuation 0: the run as it happened`,
so a plain run answers about that one valuation. A zero exit code proves nothing.

## 7. Worked example: HDFS-17960

[Hadoop PR #8672](https://github.com/apache/hadoop/pull/8672). The NameNode decrements
`numSnapshots` when replaying a snapshot-deletion edit even if the snapshot was already gone,
so the counter and the list disagree and the next checkpoint throws from the snapshot-count
check in `FSImageFormatPBSnapshot.Saver.serializeSnapshotSection`.

The case declares one root — the `dfs.namenode.snapshot.deletion.ordered` value the restarted
NameNode caches, published by the workload's symbolic-source hook — and one region input, the
return of `SnapshotManager.getNumSnapshots()` inside the serializer. No communication mapping:
the divergence is local to one node, so the seed session has no exports and no attaches. The
workload records deletion edits with ordered deletion enabled, restarts the NameNode, then
checkpoints, so the recording takes the **healthy** arm and its fatal predicate is concrete.
The seed publishes 90 activations, 1,113 decisions, 66 writes, 38 reads, one root and two
target rows. Wave 0 proposes **four** obligations — the serializer's own guard and the
ordered-deletion guards of the deletion region, including two distinct occurrences of one site
— and wave 1 is a fixed point. Three paths reach composition: two focused sessions that
observed the fatal arm, and the seed, which did not. The chain, as `candidate.smt2` states it
(the integer wrappers elided):

```
ordered = false                        (= M_Z_field_SRC…SnapshotManager false)
 -> the unordered deleteSnapshot arm runs twice
 -> the snapshot list keeps 1 element  (= (and (<= 0 1) (< 1 (indexed_size container_dag…))) false)
 -> numSnapshots = 0+1+1-1-1 = 0       (= M_I_field_…AtomicInteger (- (- (+ (+ 0 1) 1) 1) 1))
 -> the serializer wrote 1, reads 0    (not (= 1 M_I_field_…AtomicInteger))
```

The counter is a container-crossing state variable whose versions carry the two
`getAndDecrement`s, the list is a lowered container expression, and the fatal predicate is
their disagreement. Thirteen state families stand behind those joins, every arm attested. The
third path is the seed's own, at `ordered = true`, and composing it is honest about what it is:
asked alone with every root free it is unsatisfiable, so it is published as one `DIAGNOSTIC`
`PATH_SELF_CONTRADICTORY` row — its container joins refute the fatal read whatever the marker
is, so it contributes nothing, and the claim is found on the other two.

```
valuation 0  SNAPSHOT_DELETION_ORDERED = true   unsat   (the run as it happened)
valuation 1  SNAPSHOT_DELETION_ORDERED = false  sat     selected path 352bc6c4…
claim: MARKER_FLIPPED at valuation 1, movedRoots {SNAPSHOT_DELETION_ORDERED: false},
       polarityDecides true, FINAL_READY, 0 blocking gaps (247 diagnostic rows)
```

The unsat core of valuation 0 names the three path disjuncts, the target disjunction and the
valuation assertion: the recording's own polarity is what closes it, which is exactly what
`polarityDecides` requires. The committed artifacts of that campaign are under
`experiments/hadoop/hdfs-17960/artifacts/` — the census and the claim block above are read off
them, the family and diagnostic counts off a fresh composition over the same corpus — and
`experiments/hadoop/hdfs-17960/README.md` reads them row by row.

## 8. Status and limits

Six cases are prepared, in four case directories (HDFS-17899 carries three, one per request
flow). HDFS-17960 passes cleanly end to end under the current design: one campaign, the claim
above, no blocking gaps, and the unpinned probe answering sat at the buggy polarity and unsat at
the other. HDFS-11741 — two nodes, where the Balancer caches a data-encryption key a DataNode
then cannot find, and the witness needs two clock-driven flips on two nodes — exercises the
multi-node path: the seed passes the gate, the closure reaches the DataNode's key map through
the declared wire port and the map's static write sites, exploration converges in two waves,
every family arm is attested and every composed path names a clock. It does not yet publish an
accepted claim. The composition over the last 11741 corpus is decided in seconds; every
valuation is satisfiable, including the recorded one, because two focused sessions carry the
key-serial root's symbol without its mint row (minted at NameNode startup outside any admitted
activation) — the R4 to-do; a witness needs a recording made after it.
The other four cases are prepared and not yet run.

Known limits, stated plainly:

- **Structural identity is exact about iteration counts.** A replay running one more or fewer
  iteration of a loop on the index path re-addresses everything after it, and the campaign
  refuses the affected tasks rather than matching approximately. Aligning such a loop by a
  declared monotone per-iteration value is a designed extension, deliberately unused: every
  candidate so far turned out to be an engine defect, not real nondeterminism.
- **Work started inside unwoven JDK internals degrades.** Activations whose scope cannot be
  attributed are addressed `Lost` — an identity, but a weaker one. They are counted and
  reported (`LINEAGE_LOST`); closing them to zero is an open goal.
- **The static graph names its cells after Soot locals.** Soot's `LocalSplitter` walks an
  identity-ordered worklist, so two analyses of the same bytecode can name one cell `$z12` and
  the next `$z13` and the candidate graph's digest moves although nothing in the program or in
  this engine did. It changes no claim — every collection of ours is insertion-ordered — but it
  makes the static artifact unusable as a regression digest on its own.
  Local cells are still named by Soot-generated local names, which the `LocalSplitter` assigns
  in identity-hash order, so `candidate_dataflow_edges.jsonl.gz` is not yet a pure function of
  the workload — the PC4 to-do.
- **Declarations are per case and manual, and fail-closed means a new case's first campaigns
  get refused.** Roots, ports, loop bounds and the target occurrence are the case's assumptions
  and are what the result is *about*; nothing infers them. Until they are complete and the
  nondeterminism is pinned, the case is refused by name — a declared input whose method no
  region covers, a loop with no bound, a root the recording mints nowhere, an assignment no
  replay planted. The refusals are the checklist.
- **The result is about the bounded model the case declared.** An incomplete search is not a
  whole-program proof; a closed `UNSAT` additionally requires complete propagation,
  container-state, path and topology coverage, and a satisfiable witness is a statement about
  the paths the corpus contains.

## 9. Where this stands, and what to do next (2026-09-16)

This section is the handover. `docs/HANDOVER.md` is the operational companion —
repo layout, how to build, how to run a case — and should be read first if you
are about to run something rather than change something.

**The machine this was developed on has been decommissioned.** Nothing outside
this repository survived. The two corpora the offline gate ran against, the
built VM image and the Hadoop workload trees are all gone and must be
regenerated; `docs/HANDOVER.md` says how, and what it costs.

### What round 3 merged

Round 3 was a cleanup pass: one implementation per notion, every refusal named,
every deleted member's readers checked first. In merge order:

- **R2** — the runtime's dead members and its unnamed refusals: members nothing
  read deleted, every remaining refusal filed by name.
- **PC** — `edgeBindings` became `exportConsumers`; the target cutoff is gone.
- **R1** — `ConcolicRegionRuntime` split into 11 classes along what each one
  owns, no behaviour change.
- **C** — the composer's fail-opens closed, plus items P1 and P4.
- **PC2** — finalizer cluster D deleted; admission is by *declared capture*;
  `IMPORT` now runs per wave as well as on the seed.
- **R3** — a focused mint states its `recordedValue`; the `seq` rule.
- **DOC1** — the acceptance harness (`experiments/hadoop/accept`).
- **C2** — attestation reduced to one rule; the P3 closure; `EXPLORE`'s
  refusals named.
- **DOC2** — the docs made to describe only mechanisms that exist.
- **PC3** — a declared port is the scope map's `DECLARED_SITE` joined with the
  recording's own return/argument captures, minted by `SymbolicInputSelection`.
- **C3** — family-only binding of wire arrivals (section 5); 11741's
  composition went from timing out to decided in about 7 seconds.

### What landed unvalidated, and what is still a patch

Three round-3 branches were unfinished when work stopped. Their **committed**
work is merged into this history so it is not lost; their **uncommitted,
mid-edit** work is preserved as patches under `docs/wip/<name>/`, unapplied.
Each directory has a `NOTES.md` with the mandate, what landed, what did not,
and the definition of done.

| branch | merged | still a patch |
|---|---|---|
| `FIX1` | 3 commits: the wave `IMPORT` gate reads the whole epoch roster; a term is judged at the valuation its session RAN under; a verdict is fail-closed on the rows its session carries | item 4 — *why* session `793875fb482a10a4-4b39d011`'s flip prefix stopped matching. The patch's answer (ask the flip's question only of the occurrence the obligation addresses it at) is written and tested but never measured against the refused corpus |
| `PC4` | 2 commits: PLAN's region-scoping walk is fed by declared ports and the scope map's stored cells; finalizer clusters B/C/E, `CONCRETE_STRUCTURE_CARRIER` and the CONCRETE rows deleted (`RuntimeSelectedRegionFinalizer` 3702 → 1634 lines) | items 3 and 4 — deleting `RuntimeRefinedGraphBuilder`, `RECORD_FIELD`/`instrumentFieldTrace`, `trace.fields` and `refined_dataflow_edges.jsonl.gz`; and naming local cells by the program variable |
| `R4` | 1 commit, a measurement that changes no code: a root symbol with no `RootMintRow` comes from an *abandoned activation*, and nothing refuses it anywhere | all four repairs — the runtime's `MINT_UNATTRIBUTED`, the `IMPORT` invariant, `UNATTESTED_ARM` in `Arms.arm`/`ComposedFamilies`, and the `CLOCK_SKEW` PASS rule in the harness |

**These three merges have NOT been validated by a live acceptance campaign.**
They were judged offline — the gate below, the suite, and `ImportGateMain` over
the two kept corpora — and nothing more. Treat their correctness as a claim
about artifacts, not about a run.

One deliberate deviation to know about: the retention ruling asked for 11741's
`region_path_max_tasks` to be raised to 256. PC4 raised `schedule_max_jobs` to
256 instead and left `region_path_max_tasks` at 128, on the argument that
`schedule_max_jobs` is the cap the scheduler actually refused on ("exceeds max
jobs") while `region_path_max_tasks` bounds `EXPLORE`'s wave closure. Both
wave-0 artifacts are byte-identical across the change, which is the evidence
offered for it. If a later wave refuses on the closure bound, this is the first
thing to revisit.

### Acceptance state

- **HDFS-17960 passes offline on the kept corpus** — the claim in section 7,
  `blockers=0`, `FINAL_READY`. Every `wave0` and `compose` gate row is
  byte-identical across the three merges above, so those merges do not disturb
  this claim.
- **The last LIVE 17960 run was refused** — by the new per-wave `IMPORT` gate,
  which is what `FIX1` is about. Items 1–3 of `FIX1` are merged; item 4 is not,
  so a live run may still be refused. This is step 1 of the minimal delta below.
- **HDFS-11741** composes in seconds and is satisfiable at *every* valuation
  including the recorded one, so it yields no witness. The cause is measured and
  is step 2 of the minimal delta below. **The existing 11741 corpus cannot be
  repaired offline** — the rows the fix publishes were never written — so a
  fresh recording is required.
- **HDFS-17897 and the three HDFS-17899 flows are prepared and have not been
  run.**

### The minimal delta (2026-09-17)

**The principle**, in three rules the architecture already assumes and the code must now apply
everywhere. (1) **External ins are decided by tracing**: an occurrence's external ins are its reads
of a location another occurrence wrote or that a static write site in another region can write, plus
its wire attaches and declared roots — never whichever reads happened to find a symbolic value. (2)
**Every external in is a placeholder symbol** in that occurrence's focused replay, including where
the recording wrote a constant. (3) **A producer occurrence's arm binds ALL its outs on ONE
selector** — one arm per session path of that occurrence, carrying every export and every write with
its π and its valuation, so selecting an arm pulls in that occurrence's own external ins
recursively. A family is, for one external in, the arms of the occurrences that write it, exactly
one selected; ordering constraints — the selected writer before the reader, no other selected write
in between — only where a location has several writer occurrences.

So linked replay, chain templates and reorder bounds are not needed; a loop is many occurrences, one
root context (`Root:<role>/<api>#k`) per tick; the "tree" is only a view that defines the
external-in set and the causal context. The false positive rule 3 prevents: A writes constant
`mode=FAST` under `x>0` and exports `n=y`; C reads `mode` and `count`. If `mode` stays concrete, z3
picks A's `x<=0` arm for the export while C still sees `FAST` — a witness `{x:-1}` no execution has.

**Where the code deviates today.** Admission is by declaration only (`plan/ConcolicScheduler.java`,
`SymbolicInputSelection.decide` marks an undeclared read `CONCRETE`/`UNDECLARED`) — rule 1
unimplemented. A declared container cell cannot mint (`runtime/RootMint.java`,
`declaredContainerCell`), blocking rule 2 for `allKeys[keyId]`-shaped reads. State arms are
same-session only while wire arms are cross-session (`smt/Arms.java`, `stateArms` vs `wireArms`),
and `stateArms` keeps only an occurrence's last write. A state read is joined to the observed
version as an unconditional conjunct and single-writer locations get no family
(`compose/Composer.java`, `compose/ComposedFamilies.java`). And a location written before the
recording window has no writer occurrence in the corpus — 11741's `SERIAL_NO` and pinned keys — and
is today silently a literal.

**The delta, in order.** (1) Apply `docs/wip/FIX1`: the per-wave `IMPORT` gate over the whole
roster, `RowInvariants.decisions` judged at the valuation the session ran under, a focused session
whose prefix did not match or whose root never minted `NOT_ADMITTED` — target, 17960 live PASS. (2)
Apply `docs/wip/R4` plus the pre-window rule: a root symbol without its `RootMintRow` is refused —
the runtime keeps the value concrete and publishes `MINT_UNATTRIBUTED` when no admitted activation
owns the mint, a new `IMPORT` invariant requires a mint row for every referenced root symbol, the
composer refuses such an arm (`UNATTESTED_ARM`); and a location written before the window is an
external in with an empty family, so a declared root or a named refusal. (3) Compose only,
offline-verifiable: one selector per (producer occurrence, session), shared across its families
— **done**; still open in this step: a family at every closure-reached external read,
single-writer locations included; no pin to the observed version; all of an occurrence's writes
kept. (4) Φ by tracing: PLAN publishes a new
`PLACEHOLDER_SITE` row in `static_scope_map.jsonl` — the same family and readers as today's
`DECLARED_SITE` — and the runtime mints there through the existing declared-site path
(`plan/DeclaredSiteCapture`, `runtime/SymbolizeAction`); container cells may mint, bound to the
container-state symbol. (5) Cross-session state arms — `Arms.stateArms` over the writer occurrences
of every session — needs producer-side object identity, the one substantial engineering item. (6) A
materialization gate in `DECIDE`: a satisfiable witness is run once with its global root assignments
and no branch override, and must reach the target.

Steps 1–3 should suffice for HDFS-11741's witness: its only multi-writer location has one in-window
writer per node, and the witness is two arms — dn1's refresh removing the expired key, nn0's second
rotation no longer exporting it — joined at the `block-key-id` handoff. Steps 4–6 make the method
general. Two facts from that case's workload tree: the two NameNode rotations are forced by the
workload under a `KEY_MANAGER_TICK` root — two `master.updateKeys(Long.MAX_VALUE)` calls inside
`TestCausynthExpiredBalancerKey`'s recorded window — not by the heartbeat monitor, whose
`keyUpdateInterval` never elapses there; and the Balancer mints its data-encryption key locally from
its own `BlockTokenSecretManager` (`KeyManager.newDataEncryptionKey`), receiving the NameNode's key
only over the declared `block-key-id` port.

### The to-do, in order

1. **Steps 1–3 of the minimal delta above.** `docs/wip/FIX1` (`git apply
   uncommitted.patch`) and its item 4, then the 17960 acceptance campaign live —
   the one case known to pass, so the shortest path back to a green end-to-end
   run. Then `docs/wip/R4` with the pre-window rule and a re-run of 11741 — **a
   fresh recording is required**, not a re-composition of the old corpus. Then
   the compose-only step, which the offline gate can judge on its own.
2. **Apply `docs/wip/PC4`** and finish items 3 and 4, honouring the retention
   ruling: retention is a scope fact; keep all 15 activations of
   `REGION.16ba41cf` and all 63 of `REGION.1f6914ec`; accept a task-count drop
   only after a writer-coverage check — no dropped occurrence may hold a
   `WRITE_SITE` of a cell a retained occurrence reads.
3. **Then 17897, and 17899 bug1–3.**
4. **Steps 4–6 of the minimal delta** — Φ by tracing, cross-session state arms
   and the `DECIDE` materialization gate. These are what make the method general
   rather than sufficient for the cases above.
5. **Deferred identity items**: `Lost` context should address to an empty index
   rather than a weaker identity; carry lineage explicitly instead of through
   `InheritableThreadLocal`; give loop bodies their own iteration frames. Plus
   the bounded leaks — `FrameJournal` eviction.

### How to verify a change

**Offline, and this is the normal loop.** `ExploreMain` wave 0 plus
`ComposeMain` over a kept corpus must reproduce that corpus byte for byte. The
gate that does this is `tools/gate3/` — it runs the offline owners of the engine
over frozen corpora and writes one digest line per artifact, so a change is
judged by which digests moved and whether each one is explained. A moved row is
not a failure; an *unexplained* moved row is. `tools/gate3/GATE3-LOG.md` is the
row-by-row history of round 3 and is the model for how to account for one.

The corpora themselves are **not in this repository** and the host that held
them is gone. Regenerate one with `experiments/hadoop/accept` and point the gate
at it (`GATE3_CORPORA`); `tools/gate3/README.md` gives the command and the
two-pass invocation.

**Live:** `experiments/hadoop/accept`. `report.py` decides PASS from the claim
the engine published — `SAT_CANDIDATE`, `FINAL_READY`, no blocking gap, the
mechanism the case is known to fail by, `polarityDecides`, and a finding that
moves at least one root away from the recording.

### Working rules a continuing agent must keep

These are the owner's standing rules. The full set is in
`docs/planner-memory/` (`MEMORY.md` is the index); these are the ones that bite
daily.

- **The rows are the authority.** What a read observed, which write it saw,
  what a session ran under — all of it is answered by the published rows, never
  by an offline join over the static graph and never by a recorded receiver.
- **Fail closed, by name.** A question the corpus cannot answer is a named
  refusal with a registered gap code, not a default, a cap, a heuristic or a
  synthesized value. Register new codes in `GapLedger`.
- **No compat layers. Delete first.** A superseded mechanism is deleted
  outright — no adapters, no stubs, no second spelling kept alive. Before
  deleting a published member, list its readers with `git grep`.
- **One implementation per notion.** If two places answer the same question,
  that is the defect; consolidate before fixing either.
- **Every fix is stated for its whole class.** Trace it through rows → explore →
  compose → claim, say what the class is, and add the invariant to the `IMPORT`
  gate. Stopping at the second symptom is how the duplicates got here.
- **Keep the suite small** — at most 100 `@Test` methods; there are **46** now.
  New behaviour folds into an existing test rather than adding one.
- **Never edit a kept corpus in place.** `ExploreMain` writes `slots.jsonl`
  beside `--sessions`; copy the corpus before experimenting on it.
- **Never rebuild a Hadoop tree while a campaign is running on it.**
- **Verify a branch tip with `rev-parse`** before claiming anything about it.
