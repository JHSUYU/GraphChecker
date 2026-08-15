# HDFS-11741

This experiment runs the automatic bounded GraphChecker pipeline against the
Hadoop revision immediately before the HDFS-11741 fix:

```text
ece33208b89a6a06c1b362d10fab31343fe5df13
```

Start from that revision or an audited descendant which does not commit a
`KeyManager` rewrite. The experiment applies one canonical runtime patch
(trace context, bounded workload knobs, and deterministic block-key serials)
plus the fatal-target marker. `HDFS11741_VARIANT` selects the program semantics:

- `vulnerable` (default) requires the original null-only encryption-key guard.
- `patched` adds only `encryptionKey.expiryDate < Time.now()` to that guard.
- `patched-fault` adds the same guard and an explicit symbolic-RPC-fault patch.
  It fails before changing Hadoop while that second patch is unavailable.

The RPC hooks carry trace lineage only; endpoint, payload, and value
fingerprints are not part of the binding protocol.

The supported commands are:

```bash
# Patch/build Hadoop, construct its test classpath, and run the concrete test.
HADOOP_REPO=/opt/hadoop experiments/hdfs/hdfs-11741/run.sh prepare

# Automatic static analysis + two runtime passes + task generation.
HADOOP_REPO=/opt/hadoop experiments/hdfs/hdfs-11741/run.sh tasks

# Rebuild only the exact target-first schedule from existing analysis outputs.
HADOOP_REPO=/opt/hadoop experiments/hdfs/hdfs-11741/run.sh schedule

# Resume from a current indexed task plan: bounded summaries, SMT, and Z3 only.
HADOOP_REPO=/opt/hadoop experiments/hdfs/hdfs-11741/run.sh candidates

# Complete pipeline: prepare, task discovery, bounded summaries, SMT, and Z3.
HADOOP_REPO=/opt/hadoop experiments/hdfs/hdfs-11741/run.sh full

# Run the fixed-code experiment in its own artifact tree.
HDFS11741_VARIANT=patched HADOOP_REPO=/opt/hadoop \
  experiments/hdfs/hdfs-11741/run.sh full
```

All experiment artifacts are rooted at `experiments-output/hdfs-11741`
(override with `HDFS11741_WORK_ROOT`). Non-default variants use
`experiments-output/hdfs-11741-patched` and
`experiments-output/hdfs-11741-patched-fault`, so their analysis, replay, and
SMT artifacts cannot be mistaken for the vulnerable run. These roots remain
outside `target/` so `mvn clean` cannot erase a recorded campaign. A vulnerable
tree recorded before this change under `target/hdfs-11741` is still honored
with a warning; migrate it once with:

```bash
mv target/hdfs-11741 experiments-output/hdfs-11741
```

`config` and `validate` are read-only diagnostics. `traced-workload` is an
internal callback used by `workflow.properties`; it is not a separate workflow.
There is no public single-task, single-region, or single-target selector.

`tasks` stops before concolic execution and produces:

```text
experiments-output/hdfs-11741/runtime/concolic_region_plan.jsonl
experiments-output/hdfs-11741/schedule/execution_task_plan.jsonl
experiments-output/hdfs-11741/schedule/branch_queries.jsonl
experiments-output/hdfs-11741/schedule/runtime_workflow_schedule_index.json
```

Scheduling is target-first. It takes the highest-ranked valid fatal target,
walks its trusted exact-port dependency closure, and schedules only that one
target goal plus the unique producer logical goals in the closure. Each goal
is selected with its region, runtime occurrence membership, and goal identity;
the occurrence is discovery evidence, while the emitted task retains the
logical replay identity. The runtime plan owns compact region ports and flat
edge evidence once; goals refer to edges by id. The scheduler parses it once,
materializes the target and all producers from one in-memory index, and writes
the compact workflow index last as the schedule commit record. `candidates`
requires that record and verifies its region-plan/task-plan hashes, task set,
goal kinds, admissions, exact occurrence membership, and producer projections;
a missing, stale, or malformed index fails closed rather than reparsing the
large plan through a compatibility path.

When several selected scalar goals come from the same exact producer
invocation and path seed, the scheduler emits one atomic producer task. Its
`selectedGoals` ledger retains every original goal and projection, while the
task carries the union of their real outputs and edges. Versions emitted at the
same invocation are captured in one relation rather than combined as an
independent Cartesian product.  An earlier field write and a later accessor
read on the same runtime object are connected by an ordinary exact field
read-from edge; accessors such as `getKeyId()` have no HDFS-specific rule.

### End-to-end model used by the current run

The current implementation turns the recorded passing workload into the SMT
in the following order:

1. `target.yaml` and the static graph provide candidate fatal/control sites,
   RPC mappings, fields, and region boundaries. Static reachability alone does
   not choose a symbolic variable.
2. The runtime trace selects exact activations and accesses. Schema-4 boundary
   rows flatten configured RPC object/array leaves such as
   `allKeys[i].keyId` and `allKeys[i].expiryDate`; each row retains its RPC
   occurrence, producer/consumer root, boundary sequence, array path, receiver,
   process, and declaration. The concrete array shape chooses which observed
   element leaves exist in this bounded case; the array reference itself is not
   replaced by an unconstrained symbolic array.
3. Target-first discovery follows the selected fatal input closure through the
   two RPC reader chains and the cold-to-cached `KeyManager` state chain. An
   exact heap handoff between two selected occurrences of the same logical
   producer outranks unrelated guard count, which selects the cached-key target
   without a Balancer/DataStreamer name heuristic.
4. Goals from the same exact `updateKeys` invocation and path seed are scheduled
   as one atomic relation. Its `selectedGoals` ledger preserves the individual
   projections, while its closure contains their joint output set. This keeps
   correlated Map/key outputs from one invocation together.
5. Concolic replay symbolizes only the exact selected scalar/accessor inputs.
   It executes the bounded loops and container operations and captures the
   resulting relation at the semantic output boundary. Branch flipping changes
   the path through that bounded invocation; it does not cause the engine to
   synthesize an unobserved RPC interleaving or silently substitute a different
   heartbeat snapshot.
6. For state propagated inside the atomic invocation, the scheduler matches an
   earlier selected field write to a later accessor read using exact receiver
   identity, full declaration, and `writerEventSeq < readerEventSeq`. Replay
   seeds the recorded primitive only when no solver assignment exists. The
   importer removes just that seed equality when the exact producer edge owns
   the symbol, preserving every subsequent guard/container predicate.
7. The composer binds RPC, shared-state, and intra-invocation read-from edges,
   emits the fatal prefix, and follows exact equalities (including proved
   split/parse aliases) back to canonical target ports. It fails on a missing
   confirmed edge, but does not require unrelated summaries or manufacture a
   producer for an honest pre-state root.
8. Z3 checks the composed candidate. Boolean roots are exhaustively projected;
   integral existential roots are audited by fixing the complete SAT witness
   and perturbing one coordinate. One `unsat` neighbor proves the root space is
   constrained, while a finite set of `sat` neighbors would remain explicitly
   inconclusive rather than being called exhaustive.

This is bounded observed-path semantics. Replay preserves the selected causal
case; it does not claim systematic exploration of all NameNode/heartbeat/
Balancer interleavings. If an exact RPC occurrence, array shape, or selected
boundary cannot be reproduced, that replay produces no relation for the case
instead of being alpha-renamed into a different occurrence.

## Current patched-run result

The CLOSED-trace completion queue is finished.  The current commit record
selects target `call3191805` and eight producer tasks.  All nine seed/path sets
closed; composition resolves 20 selected transport/state edges plus two exact
same-invocation field read-from edges (22 total) with zero gaps and writes a
`CANDIDATE_READY`, closed-path-set `candidate.smt2`.  The cold and cached
Dispatcher occurrences are `3180179 -> 3186426`; the joint NameNode relation is
`call2454593`; the exact later key construction is `call3079981` and contributes
the trace-grounded constant `keyId=11746`.

The canonical campaign is:

```text
experiments-output/hdfs-11741-patched/candidates/
  REGION.61e62f41-34c6-3a5d-b610-b639dc3f4838-call3191805-c5b0d5ca/
```

`/usr/bin/z3` returns `SAT / REACHABLE` for the automatic query in about 0.62
seconds.  Its Boolean projection is `true` because the closure has no free
Boolean root, and is explicitly labelled
`BOOLEAN_PROJECTION_EXISTS_NON_BOOLEAN_ROOTS`.  The scalar-root audit perturbs
the complete satisfying witness one integral coordinate at a time; changing
the first `expiryDate` from `Long.MAX_VALUE` to `Long.MAX_VALUE-1` is `unsat`,
so the published verdict is `CONSTRAINED_ROOT_SPACE`.  The result remains
`CANDIDATE_ONLY`, not a complete real-world HDFS witness, because this finite
counterexample proves non-degeneracy without exhaustively projecting the
infinite scalar domain.  The solver-native binding audit is `AUDITED`: the
relation-only baseline is `sat`, the vacuity guard passes, and both fatal
operands are exact target-port occurrences bound to recorded producer versions
with load-bearing edges.

The key correction is deliberately small: a primitive output with no symbolic
inputs uses its exact recorded value; symbolic producer outputs continue to
use their real VM expression and exact invocation grouping.  When an exact
same-invocation producer edge supplies a field input, the importer drops only
the VM's replay-heap initialization equality for that symbol and retains every
later branch and container predicate.  This prevents a drifted replay Map key
from being joined to a trace-exact field relation.  No HDFS method name, call
id, lifetime formula, output-version rank, or producer Cartesian product was
added to the engine.

`full` does not hard-code thread ids, object ids, call ids, or HDFS region
names. Each selected task is instrumented and run by the bounded execution
engine; the importer and composer consume those summaries directly. Campaign
and merged summaries remain below
`campaigns/auto-seeds/{target,producer}/<task>/`. The canonical composition is
retained at:

```text
experiments-output/hdfs-11741/candidates/<campaign>/candidate.smt2
experiments-output/hdfs-11741/candidates/<campaign>/composition.json
experiments-output/hdfs-11741/candidates/<campaign>/z3-result.json
experiments-output/hdfs-11741/candidates/<campaign>/result.json
experiments-output/hdfs-11741/candidates/sat-result.json
```

The last path is a convenience copy of the most recently published reachable
result. The campaign-local four artifacts and the current schedule index are
the authority; an unreachable later campaign does not turn an older pointer
into evidence for the new schedule.

Run the solver-native binding audit on a completed campaign without editing
its formula. It consumes the composer's operand ledger, removes every
exact named assertion recorded as fatal-dependent (including the mutation
witness) to establish a satisfiable relation-only baseline, then proves each
operand's own path prefix satisfiable before emitting its pin and runtime-edge
ablation queries:

```bash
campaign_dir=experiments-output/hdfs-11741/candidates/<campaign>
experiments/hdfs/hdfs-11741/solver_binding_audit.py \
  --smt "${campaign_dir}/candidate.smt2" \
  --manifest "${campaign_dir}/composition.json"
```

The versioned report and all derived SMT files are written under
`<campaign>/solver-binding-audit/`. A relation-only result other than `sat` is
reported as `NON_AUDITABLE_RELATION_BASELINE`; operand pins are not evaluated
in that state, which prevents an already-unsatisfiable final query from
vacuously passing every binding check. The command exits 0 only for `AUDITED`,
1 for `AUDITED_WITH_FINDINGS`, and 2 for an inconclusive/non-auditable run.

To expand a SAT path-flip result into the concrete DataNode time ordering,
run the branch reporter on that task's query:

```bash
experiments/hdfs/hdfs-11741/branch_relation_report.py \
  --smt <path-flip-task>/path_flip_query.smt2
```

It restores the Java comparison to `expiry < T_recv`, labels the final
predicate as the flipped target, and prints only the expiry/time values needed
to explain the branch. It reports UNSAT without requesting a model.

Concolic execution keeps two bounded parallelism levels. Independent logical
region campaigns run in parallel (`HDFS11741_REGION_JOBS`), and one campaign
executes the sorted semantic path-seed/branch-flip frontier in parallel
(`HDFS11741_PATH_JOBS`). Both default to this host's CPU count, and the two
levels multiply: a campaign fan-out of N with a flip fan-out of M admits N*M
concurrent replays at roughly 1 GB resident each. Setting either to 1
serialises that level; the run then produces byte for byte the same artifacts,
only hours later, so each fan-out announces the width it is actually using and
warns when that width is 1 or was defaulted. Those lines land in
`experiments-output/hdfs-11741/run-<stage>-<timestamp>.log`, which is the only
place the width of a finished run can be read back from. Every campaign and
flip has a private classes, test-data, log, result, and summary directory.
Frontier
results are merged serially by canonical query key, and only the coordinator
performs partial-SAT probes, so concurrency does not change the composed
relation order.

Replay-cache identity includes the selected variant and deterministic digests
of the compiled HDFS main, test, and instrumented class trees. Rebuilding or
changing the patched program therefore cannot reuse a vulnerable execution
summary.

All loops in a concolic task use the generic CFG-backedge limit of eight body
iterations; this applies to service loops without recognizing Hadoop method
names. The three HDFS workload activation knobs default to four.
`HDFS11741_NN_UPDATE_ITERATIONS`,
`HDFS11741_DATANODE_REFRESH_ITERATIONS`, and
`HDFS11741_BALANCER_REFRESH_ITERATIONS` may reduce that concrete evidence
window to 1--8; values above eight are rejected. Container materialization
currently retains up to 32 failure-relevant cells per logical input port; this
is an independent exploration resource cap, not an assumption that an HDFS
container has length 32 and never a way to increase loop execution.

The concrete workload is:

```text
org.apache.hadoop.hdfs.server.balancer.TestBalancerWithEncryptedTransfer
  #testEncryptedBalancer1
```

The protocol mapping in `protocol-stubs.jsonl` declares the logical RPC pairs
and whether a server callback starts a new execution entry or remains nested in
its owning region. Schema version 2 also declares the bounded scalar leaves at
each request/response boundary (`leafId`, direction, port, declared field path,
and container bound). Trace schema 4 records those leaf cells, completion
counts, and explicit gaps directly on both sides of the configured exchange.
The refiner accepts only complete, configuration-matching evidence; missing,
mixed, stale, or ambiguous cells become durable blockers for the selected
demand. The former reference-array snapshot and carrier-reconstruction path is
retired. Runtime trace lineage chooses the actual occurrences; wire payload
equality is deliberately not revalidated.

The lightweight patch gate uses a temporary clean checkout and tests first and
idempotent second application:

```bash
experiments/hdfs/hdfs-11741/test_patch.sh
```
