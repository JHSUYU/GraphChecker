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
or stitches an input to an output.

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

**Fail closed, by name.** Every refusal is a gap row of a closed kind, classed `BLOCKING` (the
stage fails, naming the row, field and owner) or `DIAGNOSTIC` (recorded, the campaign goes on).
No cap, default, heuristic match or synthesized value anywhere.

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
point. HDFS-11741, two nodes and 84 planned tasks, proposes **36** in wave 0 and reaches a
fixed point in the next wave; before an obligation's identity became `(task, site, ordinal,
outcome)` *owed once across the corpus*, the same nine flips were re-proposed 706 times in one
wave.

## 3. The pipeline

One campaign per case, driven by `run_engine.sh`. Inputs are frozen before any work, and each
iteration (topology **epoch**) writes its own immutable directory and composes its own answer.

| Stage | Consumes | Produces | Gate |
| --- | --- | --- | --- |
| `PREFLIGHT`, `FREEZE_TOOL`, `SETUP`, `FREEZE` | workflow config, jar, workload tree | frozen inputs, reserved campaign root | an unknown workflow key, or a campaign root already holding a run, is refused by name |
| `SEED` | workload command, stock JDK 8 | recording trace, region skeletons, candidate graph | recording opens only after the workload registers its stable node sources |
| `PLAN` | recording, declarations | `static_scope_map.jsonl` (write sites per demanded location, export sites per port, guard set per target site), `execution_task_plan.jsonl`, the declared target resolved to a full address | a declared input whose method no planned region covers is refused; one plan row per planned occurrence |
| `INSTRUMENT` | skeletons, static scope map | instrumented classes | every woven body is validated, then JVM-verified fail-closed |
| `REPLAY` (seed) | instrumented classes, custom VM | the seed **session**: one file per row kind plus its expression table | frame pushes and pops pair one-for-one (`FRAME_UNBALANCED`) |
| `IMPORT` | the epoch's sessions | gap rows | the row contract, checked here and nowhere else (§5); `BLOCKING` fails the campaign |
| `EXPLORE` | every session so far, static scope map, root domains | per wave: `obligations.jsonl`, one focused session per obligation, `obligation_results.jsonl` | an unbound symbol in a flip model is `UNPRODUCIBLE_ANSWER`, never sat; a solver error is `NOT_ADMITTED`, never unsat; an arm a session already recorded is not re-flipped |
| `COMPOSE` | the corpus, families, root domains | `candidate.smt2`, `candidate_composition_manifest.json` | a projection that joins no version and pins no value is `UNSTATED_VALUE` and refuses |
| `SOLVE`, `DECIDE` | the composed query | a z3 answer per valuation, `claim.json` | satisfiable at the recorded valuation on a healthy recording is a blocking alarm; a witness moving a root inside an unattested arm is refused |
| `EMIT` | all of the above | `result.json`, `gaps.json`, `run-manifest.json` | acceptance is the claim **and** the named gaps together |

`EXPLORE` runs in waves: one JVM plans the wave — reading every session the epoch has produced
and writing the obligations the frontier is owed — and one worker per obligation runs a focused
replay. The closure is recomputed from scratch each wave, so a producer that became reachable
only through last wave's flip enters this one. Both stops are coverage telemetry, never a
failure: a wave proposing the same obligations with the same verdicts has learned nothing, and
an unexplored sibling blocks a closed `UNSAT` while saying nothing about a satisfiable witness.
A replay pairing an endpoint this epoch's catalog lacks is a `TOPOLOGY_DIVERGENCE`: the epoch
composes what it can read, and the *next* epoch is planned from the divergent replay's own
trace with the retained region set grown by name.

The Java side is organized by those notions: `contract` (identity, rows, the `IMPORT` gate),
`causynth` and `plan` (static analysis, scope map, task plan), `runtime` (recording and replay
hooks, row publication, the VM broker), `explore` (closure, obligations, flip queries, waves),
`compose` (disjuncts, lowering, claim policy), `smt` (expression IR, z3), `annotation` (the
target marker).

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
form from the region entry to the site. Shared state borrows Memory Indexing (FSE 2010): a heap
object's location owner is the execution index of its *allocation*, so the same object has one
name in every replay and a state edge is `(writer endpoint, reader endpoint)` needing no
cross-session version alignment; objects allocated before the window get a named degraded owner.
Two occurrences or endpoints in different replays are the same **iff** their ids are equal.

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

`IMPORT` checks ten invariants over one epoch's sessions and nowhere else, because a bad row is
not one stage's problem: a session states its role; one activation row per activation and one
row per event; a read has an observed version or a concrete value, never neither, and joins the
expression of that version or of the placeholder it minted, while no write fabricates a value;
one symbol spelling and one sort per name, every reference resolving in its own session;
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

`pi_p` is the path's recorded decision prefix, each conjunct `outcome ? term : not term`;
`phi_p` is the fatal predicate. `reads_p` joins each read to the expression of the version it
observed, or to the placeholder it minted, or pins it to the recorded value — refusing if it can
do none of the three. `joins_p` carries the boundary variables: minted root symbols, container
states `v_C` (a container crossing occurrences becomes a state variable at its first symbolic
write, every later operation a version), wire handoffs `v_H` bound through their family's arms,
per-session clock readings. `valuation_p` is what *this* path's replay ran each varied root at:
never a global fact, because one session's value asserted for all paths closes every other.

A family arm is `(producer path condition, delivered expression)`, guarded by the delivering
replay's valuation of only the roots that expression depends on. An arm whose producer never
stated a path condition is `UNATTESTED_ARM`, and a witness moving a root inside one is refused.
Root domains are exactly what the case declares: a marker free in {recorded, flipped}, an
integral root in its declared relative window, a clock with a floor of zero and no window, any
other root pinned to its recording.

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

You need stock JDK 8 and Maven for GraphChecker and the recording pass, the customized OpenJDK
8 Zero VM for concolic replay (build and smoke-test details in
[third_party/OpenJDK-Concolic-Execution-Engine/README.md](third_party/OpenJDK-Concolic-Execution-Engine/README.md)),
z3, `jq`, `python3`, and the workload's compiled classes and complete classpath. Each Hadoop
workload has its own checkout so its source changes and compiled classes stay independent, and
`experiments/hadoop/<case>/run.sh build` installs the current GraphChecker API, compiles that
tree with Java 8 and runs its concrete workload test, refusing unless exactly one test passes.

```bash
export JAVA_HOME=/absolute/path/to/jdk8 && export PATH="$JAVA_HOME/bin:$PATH"
mvn -q -DskipTests package
JOBS=4 third_party/OpenJDK-Concolic-Execution-Engine/scripts/causynth_build_in_docker.sh
```

| Declaration | Where | What it says |
| --- | --- | --- |
| the failure | `@CausynthExceptionTarget` on the constructed exception type, plus `target.yaml` | which exception construction is the failure |
| the occurrence | `declared_target_occurrence` | which occurrence of that site this case is about, as a full address — a campaign is target-directed, and the case knows which instance can fail |
| roots and region inputs | `symbolic-inputs.jsonl` | a cell whose read mints a placeholder, or a callee-level clock declaration (`<org.apache.hadoop.util.Timer: long now()>` with `"kind": "CLOCK"`) making *every* call site of that clock a root |
| root domains | `root-domains.jsonl` | per root, an absolute or relative window (`+0`/`+3`) and why. A root with no row stays pinned to its recording, which is what a case that claims nothing about it says |
| message boundaries | `communication-mappings.jsonl` | one `WIRE_FLOW` per typed producer/consumer pair, each side with a capture kind (`METHOD_PARAMETER`, `METHOD_RETURN`, `CALL_ARGUMENT`, `CALL_RETURN`) |
| loop bounds | `loop-bounds.jsonl` and `causynth_loop_default_bound` | the exact bound of each retained condition-controlled loop, with a reason. A campaign stating no default is refused; every inherited bound is published as a diagnostic gap |

The workload also carries a small tracing ABI — about twenty entry points on
`CausynthTraceRecorder`, `ConcolicRegionRuntime` and `SymbolicMessageEnvelope`: register a node
source and its aliases, open and close a request or daemon tick, carry a scope across a thread
hand-off, take and install a message envelope, symbolize a configured source. Called by name
from the workload trees against an installed jar, they are pinned as a checked test resource.

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
`cls`: `DIAGNOSTIC` describes coverage the run lacked, `BLOCKING` is why it refused. Also worth
running z3 on the published formula directly, plain and then at each polarity, which asks about
the whole formula rather than the slice the campaign solved. A zero exit code proves nothing.
[TODO: verify — the acceptance harness that scripts campaign + probe + report and checks the
case's expected mechanism is not in the repository; name its in-tree home here.]

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
observed the fatal arm, and the seed, which did not. The chain, as `candidate.smt2` states it:

```
ordered = false                        (= M_Z_field_SRC…SnapshotManager false)
 -> the unordered deleteSnapshot arm runs twice
 -> the snapshot list keeps 1 element  (= (and (<= 0 1) (< 1 (indexed_size container_dag…))) false)
 -> numSnapshots = 0+1+1-1-1 = 0       (= M_I_field_…AtomicInteger (- (- (+ (+ 0 1) 1) 1) 1))
 -> the serializer wrote 1, reads 0    (not (= 1 M_I_field_…AtomicInteger))
```

The counter is a container-crossing state variable whose versions carry the two
`getAndDecrement`s, the list is a lowered container expression, and the fatal predicate is
their disagreement. The `ordered = true` sibling is explored and composed too, and is
contradictory: with no second counter version it is not a witness for this target.

```
valuation 0  SNAPSHOT_DELETION_ORDERED = true   unsat   (the run as it happened)
valuation 1  SNAPSHOT_DELETION_ORDERED = false  sat     selected path 352bc6c4…
claim: MARKER_FLIPPED at valuation 1, movedRoots {SNAPSHOT_DELETION_ORDERED: false},
       polarityDecides true, FINAL_READY, 0 blocking gaps
```

The unsat core of valuation 0 names the three path disjuncts, the target disjunction and the
valuation assertion: the recording's own polarity is what closes it. The committed artifacts
for this run are under `experiments/hadoop/hdfs-17960/artifacts/`.

## 8. Status and limits

HDFS-17960 passes cleanly end to end under the current design: one campaign, the claim above,
no blocking gaps, and a plain z3 run on the published formula answering sat at the buggy
polarity and unsat at the other. HDFS-11741 — two nodes, where the Balancer caches a
data-encryption key a DataNode then cannot find, and the witness needs two clock-driven flips
on two nodes — exercises the multi-node path: the seed passes the gate, the closure reaches the
DataNode's key map through the declared wire port and the map's static write sites, exploration
converges in two waves. It is at its last round and has not yet published an accepted claim;
the other four cases are prepared but not yet run.

Known limits, stated plainly:

- **Structural identity is exact about iteration counts.** A replay running one more or fewer
  iteration of a loop on the index path re-addresses everything after it, and the campaign
  refuses the affected tasks rather than matching approximately. Aligning such a loop by a
  declared monotone per-iteration value is a designed extension, deliberately unused: every
  candidate so far turned out to be an engine defect, not real nondeterminism.
- **Work started inside unwoven JDK internals degrades.** Activations whose scope cannot be
  attributed are addressed `Lost` — an identity, but a weaker one. They are counted and
  reported; closing them to zero is an open goal.
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
