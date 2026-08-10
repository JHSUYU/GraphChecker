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
experiments-output/hdfs-11741/analysis/symbolic_regions.jsonl
experiments-output/hdfs-11741/runtime/concolic_region_plan.jsonl
experiments-output/hdfs-11741/schedule/execution_task_plan.jsonl
experiments-output/hdfs-11741/schedule/branch_queries.jsonl
experiments-output/hdfs-11741/schedule/selected_target_binding.tsv
experiments-output/hdfs-11741/schedule/selected_closure_bindings.tsv
experiments-output/hdfs-11741/schedule/runtime_workflow_schedule_index.json
```

Scheduling is target-first. It takes the highest-ranked valid fatal target,
walks its trusted exact-port dependency closure, and schedules only that one
target goal plus the unique producer logical goals in the closure. Each goal
is selected with its region, runtime occurrence membership, and goal identity;
the occurrence is discovery evidence, while the emitted task retains the
logical replay identity. The scheduler parses the large region plan once,
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
same semantic boundary share one version choice; they are not combined as an
independent Cartesian product.

## Current patched-run result

The CLOSED-trace completion queue is finished.  The current commit record
selects target `call3191805` and eight producer tasks.  All nine seed/path sets
closed; composition resolves 20 selected edges with zero gaps and writes a
`CANDIDATE_READY`, closed-path-set `candidate.smt2`.  The cold and cached
Dispatcher occurrences are `3180179 -> 3186426`; the joint NameNode relation is
`call2454593`; the exact later key construction is `call3079981` and contributes
the trace-grounded constant `keyId=11746`.

The canonical campaign is:

```text
experiments-output/hdfs-11741-patched/candidates/
  REGION.61e62f41-34c6-3a5d-b610-b639dc3f4838-call3191805-c5b0d5ca/
```

`/usr/bin/z3` returns `SAT / REACHABLE` for the broad automatic query.  Its
reach formula is `true` with four unenumerated existential roots, and the
generic binding audit remains `INCONCLUSIVE` for one fatal integer operand, so
the result is intentionally published as `CANDIDATE_ONLY`.  The companion
solver-only HDFS semantic probes under `manual-hdfs11741-probe/` give the
stronger experiment-specific result: the stale/expired `11746` shape is `sat`,
while adding the patched cached-key guard is `unsat`.  Their SHA-256 digests
are respectively
`bc171af13f1a3c87aa057af9864d9366d5c342f4675323f94d72433125d2a0ea`
and
`f13ace60674a5990808734722440f8d973d1134daa089fc815f22d5acd162c0b`.

The key correction is deliberately small: a primitive output with no symbolic
inputs uses its exact recorded value; symbolic producer outputs continue to
use their real VM expression and exact invocation grouping.  No HDFS method
name, call id, lifetime formula, output-version rank, or producer Cartesian
product was added to the engine.

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
