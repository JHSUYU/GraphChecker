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
| Transport and boundary scalar fields | configured declaration + schema-4 trace evidence | `TRUSTED_CONFIGURED_RPC_MAPPING_V1`, `TRUSTED_CONFIGURED_RPC_BOUNDARY_SCALAR_V1` |
| Shared state | recording + solver-chosen schedule | versioned state channel, cut points |

An auditor must be able to tell them apart; that is why the configured scalar
projection carries its own authority rather than reusing the transport's.

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

The vulnerable baseline is a frozen historical measurement. Everything in
this first table came from that baseline's automatic pipeline; it is not the
current patched schedule described below.

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
query includes the exact fatal lookup and an execution-derived removal case whose
removed member key is constrained to that lookup key.  The general
root-enumeration degeneracy probe does not enumerate all 54 existential roots;
the semantic acceptance gate is instead the pinned mutation witness above.

### Patched HDFS-11741 result (2026-08-10)

The CLOSED-trace rebuild and the completion queue above are finished.  The
current schedule contains one exact target plus eight producer tasks across
seven region templates.  It selects target `call3191805`, the cold-to-cached
Dispatcher chain `3180179 -> 3186426`, the atomic NameNode `updateKeys`
invocation `call2454593`, both configured block-key RPC reader chains, and the
exact key construction at `call3079981`.  The schedule commit record binds a
29-row region plan (`217,382,550` bytes, SHA-256
`1da5fd322854b48b0fd2441c12d9008ab444a8b382548dd0f37fa5420d8b8528`)
to a 9-row task plan (`2,112,856` bytes, SHA-256
`becbd8d2bd537688ef0646500ab6c022419265759faec2b997511c95c3230cde`).

All nine bounded replays and path sets closed.  The canonical composition is
`CANDIDATE_READY`, `pathSetComplete=true`, has zero gaps, resolves all 20
selected edges, and reports `droppedEdgeEvidenceAudit=AUDITED`.  The exact
trace-grounded `DelegationKey.keyId` write at event `3157904` is encoded as
`11746`; the selected-state edge carries it into the cold Dispatcher relation
instead of replaying an unstable service-loop occurrence.

The canonical four artifacts are under
`experiments-output/hdfs-11741-patched/candidates/REGION.61e62f41-34c6-3a5d-b610-b639dc3f4838-call3191805-c5b0d5ca/`:

| Artifact | Bytes | SHA-256 |
|---|---:|---|
| `candidate.smt2` | 5,671,051 | `39439e52ccc64cd1876d193fafb81656379cca66b652d750de736bc179df0408` |
| `composition.json` | 78,661 | `fd22d22add3c1a95d8d0a3de2a3acdb4867b8ede07ca5eda5fc18d3adb943b07` |
| `z3-result.json` | 5,278 | `b9ce0d1aa8b543189da06d7efece0b93cf16e5dde5289c85e1c878edc2c9e6d3` |
| `result.json` | 889 | `497c706e17706e7658ab911ac816ff404630b18d941691d1f963c6de46c5fcc7` |

The real `/usr/bin/z3` returns `SAT / REACHABLE`.  The automatic reach formula
is intentionally broad (`true` with four unenumerated existential roots), so
that result alone is not claimed as the HDFS-11741 witness.  A solver-only
semantic probe derived from the same fresh SMT adds the observed stale-key
conditions: cached key `11746` is expired, SASL sends `11746`, and the DataNode
table lacks `11746`.  That query is `sat` (SHA-256
`bc171af13f1a3c87aa057af9864d9366d5c342f4675323f94d72433125d2a0ea`).
Adding the patched cached-key guard makes the same query `unsat` (SHA-256
`f13ace60674a5990808734722440f8d973d1134daa089fc815f22d5acd162c0b`).
Thus the composed relations can express the bug and distinguish the patched
path without editing or replacing a producer relation.

One audit limitation remains explicit rather than hidden: the generic
solver-binding audit is `INCONCLUSIVE` because one fatal integer operand has no
exact producer-lineage record; the state operand is bound to recorded producer
versions and has a load-bearing edge.  Likewise the generic
`fatalAbsenceMutationWitness` is `NOT_APPLICABLE`.  These facts explain why the
canonical result retains `trustState=CANDIDATE_ONLY`; they do not invalidate
the zero-gap composition or the two solver-only HDFS semantic probes above.

The patched checkout and reusable evidence are:

```text
Hadoop checkout: /tmp/hdfs-11741-patched-worktree
work root:       /opt/GraphChecker/experiments-output/hdfs-11741-patched
runtime trace:   runtime/runtime_trace.jsonl             (closed, 2,477,526,886 bytes)
static graph:    analysis/candidate_dataflow_edges.jsonl (2,028,773,031 bytes)
```

The stated call ids are evidence read from the current trace and schedule, not
selection heuristics.  No Hadoop method name, call id, or line number
participates in the generic ranking rule.

## Reproduce and verify the patched result

1. **Build and verify the source.** Do not run Maven while a discovery
   or replay JVM is reading the GraphChecker jar. Run:

   ```bash
   mvn -q test
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

   Required checks: the selected fatal occurrence is `call3191805`; the
   closure contains Dispatcher calls `3180179` and `3186426`; and the commit
   index names exactly one target plus its complete exact producer closure.
   Record the actual producer count from the newly published index rather than
   copying an older count. Only demanded
   scalar/guard leaves are symbolic. The second Dispatcher summary carries the
   cached `expiryDate`, `keyId`, and recorded clock expression; endpoints,
   protobuf bookkeeping, buffer lengths, and unrelated payload stay concrete.

4. **Run bounded two-level execution, merge, compose, and Z3.** Keep the product
   of the two job counts within available memory (each replay JVM is roughly
   1 GB); four region jobs by two path jobs is a safe starting point here:

   ```bash
   HDFS11741_VARIANT=patched \
   HADOOP_REPO=/tmp/hdfs-11741-patched-worktree \
   HDFS11741_REGION_JOBS=4 \
   HDFS11741_PATH_JOBS=2 \
   experiments/hdfs/hdfs-11741/run.sh candidates
   ```

   Accept only the schedule commit record and the campaign-local artifacts:

   ```text
   experiments-output/hdfs-11741-patched/schedule/runtime_workflow_schedule_index.json
   experiments-output/hdfs-11741-patched/campaigns/auto-seeds/{target,producer}/<task>/merged_summary.jsonl
   experiments-output/hdfs-11741-patched/candidates/<campaign>/candidate.smt2
   experiments-output/hdfs-11741-patched/candidates/<campaign>/composition.json
   experiments-output/hdfs-11741-patched/candidates/<campaign>/z3-result.json
   experiments-output/hdfs-11741-patched/candidates/<campaign>/result.json
   ```

   A summary truncated before its terminating newline is invalid, not a
   partial success.

5. **Audit the result semantically.** The SMT must contain both NN reader
   chains (`updateKeys -> getBlockKeys -> Balancer` and
   `updateKeys -> sendHeartbeat -> DataNode`), the first-to-second Dispatcher
   cached-state edge, the repair guard from a real execution summary, and the fatal DN
   lookup. RPC transport may use the configured logical mapping directly; do
   not add value fingerprints or descend into protobuf. Do not handwrite key
   lifetime, rolling-key, or HDFS-specific SMT formulas. Run the existing
   solver pin/ablation checks and explain either `SAT` or `UNSAT`.  A bare
   `true` reach formula or `NOT_APPLICABLE`/zero-clause fatal mutation witness
   is a failed acceptance check even when Z3 prints `sat`.

Concolic seed replay keeps the broad 2400-second emergency budget. Path flips
have a separate 180-second default because a flip that never publishes a
selected result contributes no relation; it is recorded as
`REPLAY_PRODUCED_NO_RESULT` without changing the workload or HDFS semantics.

---

## Traps that cost whole rounds

Each of these once looked like a semantic failure.

- **A malformed cache is not reusable evidence.** `prepare_seed_campaign`
  automatically invalidates a safely scoped `TASK.SEED.*` directory when its
  replay-cache marker is absent or stale. A directory whose marker still
  matches but whose payload is malformed fails closed for manual inspection;
  the runner never silently blesses it.
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
- **Counting policy metadata as executed relation evidence.** Producer seeds
  export the symbolic input-to-output relation observed at their semantic
  boundary. Target reachability retains its exact path condition; producer
  branch-policy entries are not additional relation cases unless a replay
  actually publishes one.
