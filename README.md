# GraphChecker

> **Project scope and affiliation.** GraphChecker is a purely academic,
> non-commercial software-engineering and program-analysis research project
> maintained by a PhD student at the University of Virginia. Its static,
> runtime, concolic, symbolic-execution, SMT, and fault-modeling components are
> used only on open-source systems and authorized local test workloads to
> understand, reproduce, and repair software defects. It has no commercial
> purpose and is not an offensive-security, exploitation, penetration-testing,
> malware, or unauthorized-access project.

Automatic bounded concolic pipeline that synthesises an SMT witness for a
distributed-systems fault from a **passing** workload, and checks it with Z3.
HDFS-11741 is the case it is developed against; the engine carries no knowledge
of it. This README is the project handoff: it records the engineering doctrine,
build/run entry points, witness acceptance criteria, current state, and queue.

---

## What a correct witness looks like

The fault is two readers of one rolling table disagreeing. The heartbeat chain
decides what the DataNode **has**; the getBlockKeys chain decides what the
Balancer **presents**; the fault is the Balancer presenting a key the DataNode
has already rolled away. A witness means something exactly when **both operands
of the fatal membership test are bound to the same producer timeline**.

```
NN updateKeys()              S' = put(remove(S, expired), fresh)   one writer lane
  │
  ├─ shared field ─► getBlockKeys handler ── RPC ──► BlockKeyUpdater: addKeys
  │                                                    │ balancer's own table   [cell 1]
  │                                                    ▼
  │                                     newDataEncryptionKey (SASL send path)
  │                                                    │ cached DataEncryptionKey [cell 2]
  │                                                    ▼
  │                                     later handshakes ─► presented keyId
  │
  └─ shared field ─► sendHeartbeat handler ─ RPC ──► BPServiceActor ─► DN allKeys
                                                       │
                                                       ▼
                              DataXceiver: (assoc_has allKeys keyId) — flipped
```

Readers pick cut points on the timeline independently: Balancer at roll *i*, DN
at roll *j*, and `i < j` **is** the divergence. Cell 2 is why the lag is stable
rather than lucky — the encryption key is generated once and reused, so the
Balancer's read is pinned at the roll of its *first* handshake while the DN's
table keeps advancing.

**This paragraph is a reading, never a specification.** The relations it
describes have to fall out of symbolic execution and merging — the lifetime
arithmetic in particular is whatever executing `updateKeys` produces. Writing
that formula down instead of deriving it would skip the only thing worth
proving. Nothing in `src/` may encode a lag between readers, a lifetime
expression, or a ranking tuned to reach this story. Build the model without it
and ask whether the model admits such a solution at all. UNSAT is data, not
failure; a different story is a result to report, not a deviation to correct.

### Three evidence layers, each with its own authority

| Layer | Grounded in | Authority in the artifact |
|---|---|---|
| Relations inside a region | symbolic execution | the summary itself |
| Transport and carrier fields | declaration | `TRUSTED_CONFIGURED_RPC_MAPPING_V1`, `TRUSTED_DECLARED_CARRIER_PROJECTION_V1` |
| Shared state | recording + solver-chosen schedule | versioned state channel, cut points |

An auditor must be able to tell them apart; that is why the carrier projection
carries its own constant rather than reusing the transport's.

### Three mechanical acceptance checks, none of them case knowledge

1. **Per-symbol binding.** For each operand of the fatal condition, find the
   assertion that binds it — *with the solver, not with grep*. A symbol whose
   only assertion is its own type range is unconstrained. Pin it to a value
   outside the recorded producer versions: a bound operand goes `unsat`.
2. **Dropped-evidence audit.** For each unconstrained operand, search the
   validated runtime edges for a `CONFIRMED` edge that could have bound it.
   A hit is a named gap, never silence.
3. **Oracle rank.** The engine must rank `removeExpiredKeys()`'s removal guard
   as a flip candidate without being told what HDFS is. It reads
   `region_path_worklist.jsonl` and costs seconds — run it *before* the
   expensive stages. **Currently passing at rank 1** in both regions that carry
   the site, with all four candidates on that site.

---

## Where the work stands

The vulnerable baseline is complete. Everything in this first table is
measured from the standard automatic pipeline, not estimated.

| | |
|---|---|
| Target-first campaigns | **7 / 7** — one fatal target and six exact producers |
| Core regions | **7** — NameNode, Balancer, and DataNode |
| Closed path sets | **7 / 7** |
| Oracle rank | **1** — passing |
| Encoding faithfulness | proven: forcing the removal branch, the control `expiryDate > now` is **UNSAT** |
| `keyId` binding | proven load-bearing by Z3 ablation — delete the one line carrying the shared-state edge and the query flips to `sat` |
| Fatal absence witness | **PINNED** — one exact fatal absence/removal clause |
| NN in the `.smt` | **yes** — `updateKeys`, `getBlockKeys`, and `sendHeartbeat` relations are composed |
| Composition gaps | **0** |
| Standard Z3 result | **SAT / REACHABLE** from `run.sh candidates` |

The standard automatic entry point now completes discovery, bounded two-level
replay, path merge, closed-path composition, SMT emission, and Z3.  The SAT
query includes the exact fatal lookup and a VM-derived removal case whose
removed member key is constrained to that lookup key.  The general
root-enumeration degeneracy probe does not enumerate all 54 existential roots;
the semantic acceptance gate is instead the pinned mutation witness above.

### Active handoff: patched HDFS-11741

The current task is narrower: apply the real `expiryDate < Time.now()` repair,
run the same automatic pipeline through Z3, and report what the patched bounded
model says. `SAT` is not to be hidden or forced to `UNSAT`; it may expose a
different feasible execution or a missing real-world assumption. The required
deliverable is the solver result plus an auditable explanation of the model.

The patched checkout and reusable evidence are:

```text
Hadoop checkout: /tmp/hdfs-11741-patched-worktree
work root:       /opt/GraphChecker/experiments-output/hdfs-11741-patched
runtime trace:   runtime/runtime_trace.jsonl             (closed, 2.6 GB)
static graph:    analysis/candidate_dataflow_edges.jsonl (2.0 GB)
```

The trace contains two distinct paths through the same Balancer Dispatcher
region. The first activation (`rootCallId=3388118`) creates the cached key and
does not execute the repair guard. The second (`rootCallId=3394679`) reads that
cached key, executes the expiry guard, and sends to the fatal DataNode
activation (`rootCallId=3398578`). They are path alternatives/state steps of
one logical region, not two stable replay identities. The exact cached
`expiryDate` flow between them is already recorded; do not replace it with a
fresh free variable.

Completed source fixes that still need one frozen end-to-end run:

- Producer selection is occurrence-local, so one path seed cannot claim an
  RPC/state edge observed in another occurrence.
- Target ranking prefers exact selected slices with observed semantic guards;
  it now chooses fatal call `3398578` and Dispatcher call `3394679`, without an
  HDFS-specific name or line rule.
- Symbolization is positive-demand: exact incoming leaves, selected semantic
  guard operands, bounded state, explicit fault markers, and true root/protocol
  inputs. On the old first Dispatcher task this reduced eight symbolic values
  to two; URI ports, serialization lengths, token settings, and unrelated
  payload fields stay concrete.
- An output relation stops at its publication event. Calls begun after the
  authentication value was published are consumers, so the planner no longer
  pulls the whole handshake/RPC/server execution into that producer summary.
- Selected VM results now have a continuous finish-to-durable-append barrier;
  the JUnit runner cannot call `System.exit` while a large summary is still
  being published.
- Class-tree cache hashing is batched and preserves the old digest exactly;
  hashing roughly 11,000 classes now takes about one second rather than forking
  tens of thousands of shell processes.

## Next tasks, in order

1. **Freeze and verify the current source.** Do not run Maven while a discovery
   or replay JVM is reading the GraphChecker jar. Run:

   ```bash
   mvn -q -Dtest=RuntimeRegionPlannerTest,RuntimeWorkflowDiscoveryTest,ConcolicSchedulerTest,ConcolicRegionRuntimeTest,JUnitMethodRunnerTest test
   mvn -q -DskipTests package
   git diff --check
   ```

2. **Rebuild refinement and the region plan from the existing closed trace.**
   This does not rerun Hadoop. It should print that both pass-1 and pass-2
   traces are reused:

   ```bash
   HDFS_CP=$(tr -d '\r\n' < experiments-output/hdfs-11741-patched/project-classpath.txt)
   CAUSYNTH_REUSE_RUNTIME_TRACES=true \
   CAUSYNTH_REPO=/tmp/hdfs-11741-patched-worktree \
   CAUSYNTH_CLASSPATH="$HDFS_CP" \
   CAUSYNTH_OUTPUT_DIR=/opt/GraphChecker/experiments-output/hdfs-11741-patched/analysis \
   CAUSYNTH_INSTRUMENTED_CLASSES_DIR=/opt/GraphChecker/experiments-output/hdfs-11741-patched/instrumented-classes \
   CAUSYNTH_REGION_PLAN=/opt/GraphChecker/experiments-output/hdfs-11741-patched/runtime/concolic_region_plan.jsonl \
   CAUSYNTH_EDGE_VALIDATIONS=/opt/GraphChecker/experiments-output/hdfs-11741-patched/runtime/runtime_region_edge_validation.jsonl \
   CAUSYNTH_SCHEDULE_OUTPUT_DIR=/opt/GraphChecker/experiments-output/hdfs-11741-patched/schedule \
   ./run_engine.sh --config experiments/hdfs/hdfs-11741/workflow.properties workload
   ```

3. **Rebuild the exact target-first schedule and inspect it before replay.**

   ```bash
   HDFS11741_VARIANT=patched \
   HADOOP_REPO=/tmp/hdfs-11741-patched-worktree \
   experiments/hdfs/hdfs-11741/run.sh schedule
   ```

   Required checks: selected fatal call is `3398578`; the closure contains the
   cached-key Dispatcher path and its prior producer; all seven NN/Balancer/DN
   region templates remain represented; only demanded scalar/guard leaves are
   symbolic. In particular, the second Dispatcher summary must include cached
   `expiryDate`, `keyId`, and the VM clock expression, while endpoint, protobuf,
   buffer-length, loop-control, and container-size values remain concrete.

4. **Run bounded two-level VM replay, merge, compose, and Z3.** Keep the product
   of the two job counts within available memory (each replay JVM is roughly
   1 GB); four region jobs by two path jobs is a safe starting point here:

   ```bash
   HDFS11741_VARIANT=patched \
   HADOOP_REPO=/tmp/hdfs-11741-patched-worktree \
   HDFS11741_REGION_JOBS=4 \
   HDFS11741_PATH_JOBS=2 \
   experiments/hdfs/hdfs-11741/run.sh candidates
   ```

   Accept only the canonical artifacts under
   `experiments-output/hdfs-11741-patched/schedule/`, including
   `merged_region_summaries.jsonl`, `composed_fatal.smt2`, the composition
   manifest, reachability report, and Z3 output. A summary that was truncated
   before its terminating newline is invalid, not a partial success.

5. **Audit the result semantically.** The SMT must contain both NN reader
   chains (`updateKeys -> getBlockKeys -> Balancer` and
   `updateKeys -> sendHeartbeat -> DataNode`), the first-to-second Dispatcher
   cached-state edge, the repair guard from a real VM summary, and the fatal DN
   lookup. RPC transport may use the configured logical mapping directly; do
   not add value fingerprints or descend into protobuf. Do not handwrite key
   lifetime, rolling-key, or HDFS-specific SMT formulas. Run the existing
   solver pin/ablation checks and explain either `SAT` or `UNSAT`.

6. **Only after the patched solver result, continue cleanup.** Project demanded
   scalar RPC leaves directly at the configured trace boundary, then retire
   `ARRAY_SNAPSHOT` and carrier reconstruction together. Until that replacement
   exists, `ARRAY_SNAPSHOT` is live evidence for `BlockKey[]`, not dead code.
   Pre-project the few scheduler indices currently recovered by repeatedly
   parsing the large plan, and remove only fingerprints that add no cache or
   composition correctness property. RPC value/argument/payload fingerprints
   are already absent.

The current generated plan is known to be noisy until step 2 is rerun: the old
30-line plan is about 122 MB because whole closures are repeated. Do not treat
its roughly 500,000 expressions as inherent symbolic complexity. The measured
root cause was a post-publication call corridor plus fail-open symbolic input
selection, both fixed above.

The most recent offline rebuild was intentionally not accepted: a concurrent
`mvn package` replaced the dependency jar while the aggregation JVM was still
running, and it terminated in `NoClassDefFoundError` before publishing a new
region plan. The closed traces remain reusable and the old plan remains in
place. Start step 2 again only after the source and jar are frozen; do not
resume from or bless that interrupted attempt.

Concolic seed replay keeps the broad 2400-second emergency budget. Path flips
have a separate 180-second default because a flip that never publishes a
selected result contributes no relation; it is recorded as
`REPLAY_PRODUCED_NO_RESULT` without changing the workload or HDFS semantics.

---

## Traps that cost whole rounds

Each of these once looked like a semantic failure.

- **Retrying over failed campaign directories runs nothing.** `prepare_seed_campaign`
  refuses a half-built directory rather than rebuilding it, and also refuses
  previously-successful ones on payload mismatch. The round prints one refusal
  per campaign and executes none of them, which reads exactly like reproducing
  the failure. `rm -rf` them first; save any `hs_err_pid*.log` worth keeping.
- **Rebuilding the jar during a live run corrupts that run.** Discovery JVMs
  mmap the jar, not just campaign JVMs; one took `SIGBUS` in `libzip.so` and a
  scheduler answer came back as a literal `#`.
- **Job counts left pinned at 1** cost hours of serial execution, silently,
  because stdout never reached the work root. Both are fixed — the fan-outs
  follow the host and announce their width, and long stages log beside their
  artifacts — but the class recurs.
- **Deciding boundness by reading the SMT.** Binding equalities hide inside the
  single large fatal assert, and a channel's name carries the reader port twice
  rather than writer and reader. Both readings condemned a query that was fine.
  Ask the solver.
- **Counting `EXPLORE` policy as flip candidates.** Producer `branches[]` is
  `EXPLORE`-only by construction, so a "0% demotion rate" there compares two
  differently-built artifacts. The real candidate count comes from the worklist:
  75 policy branches, 8 actual witnesses.
