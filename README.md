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

### Current bounded composition design

The implementation is deliberately mechanical and case-agnostic:

1. **Trace exact occurrences.** Static control/data-flow supplies candidate
   regions and ports. Runtime activations, field accesses, RPC boundaries, and
   schema-4 scalar rows select exact producer/consumer occurrences, array
   indices, field declarations, and program-order coordinates.
2. **Build one target-first closure.** Discovery starts at an observed fatal
   target, follows only trusted exact edges, and retains the cold/warm state
   occurrences needed by that target. Ranking prefers an observed
   inter-occurrence state handoff before raw guard count; it contains no HDFS
   method-name or call-id heuristic.
3. **Keep one invocation atomic.** Scalar goals selected from the same exact
   producer invocation and path seed become one task with a `selectedGoals`
   provenance ledger and the union of their real outputs and edges. The
   composer never substitutes a Cartesian product of singleton summaries for
   one multi-output invocation.
4. **Replay relations, not guessed formulas.** The runtime symbolizes the
   selected exact input hooks and captures outputs at their semantic region or
   definition boundary. The importer keeps the complete relation-boundary path
   condition. When a selected producer edge defines a field input, it removes
   only the VM equality used to seed that replay heap; later branch and
   container predicates remain in the relation.
5. **Treat accessors as ordinary field flow.** Within one exact atomic region,
   an earlier selected field output and a later symbolic accessor input are
   joined only when receiver identity and full field declaration match and the
   write precedes the read. `getKeyId()` has no special rule. The resulting
   trusted read-from edge is validated and composed like any other heap edge.
6. **Compose and audit exact lineage.** RPC/state/read-from edges bind producer
   outputs to consumer inputs. Fatal-prefix equalities, including structurally
   proven `String.split`/`Integer.parseInt` aliases, carry engine temporaries
   back to exact target-port occurrences; the binding audit then checks that
   those edges are load-bearing in Z3.
7. **State the remaining freedom honestly.** Boolean roots are exhaustively
   enumerated. Non-Boolean roots stay existential; the report labels that
   projection explicitly and perturbs one integral coordinate of a satisfying
   witness. A rejected neighbor proves `CONSTRAINED_ROOT_SPACE` without
   pretending to enumerate an infinite scalar domain.

The soundness boundary is correspondingly small: never invent a producer,
never merge different exact invocations, never discard a confirmed edge, and
never interpret a finite scalar probe as exhaustive. Bounds restrict the
observed/replayed path and container state; they do not grant authority to
relations that were not recorded or symbolically executed.

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
29-row region plan (`217,414,890` bytes, SHA-256
`d8236a112980bce34ee55276d7ba3c458d27734c19a70e12fe55ccbb56fba0e1`)
to a 9-row task plan (`2,116,700` bytes, SHA-256
`3e21255bb6002d65a32e2f103cd48df50efc67e878a2a854d04c2e7d22f94548`).

All nine bounded replays and path sets closed.  The canonical composition is
`CANDIDATE_READY`, `pathSetComplete=true`, has zero gaps, resolves all 20
selected edges plus two exact same-invocation field read-from edges (22 total),
and reports `droppedEdgeEvidenceAudit=AUDITED`.  The exact
trace-grounded `DelegationKey.keyId` write at event `3157904` is encoded as
`11746`; the selected-state edge carries it into the cold Dispatcher relation
instead of replaying an unstable service-loop occurrence.

The canonical four artifacts are under
`experiments-output/hdfs-11741-patched/candidates/REGION.61e62f41-34c6-3a5d-b610-b639dc3f4838-call3191805-c5b0d5ca/`:

| Artifact | Bytes | SHA-256 |
|---|---:|---|
| `candidate.smt2` | 2,146,869 | `37f3dbb1aea5069b9a6a6fa7c5a25846a9b8f4820315afa2faf1a53ed3c4ea94` |
| `composition.json` | 83,245 | `92df12fa68e634b5887635415311a829a9bf980dd79fcce824a323b5b7604403` |
| `z3-result.json` | 6,115 | `efff53b9074ac7d825354a279ba85dcbbfac77dba3e4d046284fd86cf76fafaa` |
| `result.json` | 833 | `b0d58e384d8c0c55a076665ac532179b7a94a10aa533de8e58d039c2eb94ee60` |

The real `/usr/bin/z3` returns `SAT / REACHABLE` in about 0.62 seconds.  The
automatic Boolean projection is `true` because this exact closure has no free
Boolean root; it is explicitly labelled
`BOOLEAN_PROJECTION_EXISTS_NON_BOOLEAN_ROOTS` rather than presented as the
whole input condition.  The extractor fixes the complete satisfying scalar
tuple and perturbs one integral root at a time.  Changing the first
`expiryDate` witness from `Long.MAX_VALUE` to `Long.MAX_VALUE-1` makes the
query `unsat`, so the solver-backed degeneracy verdict is
`CONSTRAINED_ROOT_SPACE`.  This is still a bounded observed-path candidate,
not by itself a real-world HDFS-11741 counterexample.  The independent
solver-binding audit is `AUDITED`: its relation-only baseline is `sat`, its
vacuity guard passes, and both fatal operands are exact target-port
occurrences bound to recorded producer versions with load-bearing edges.  The
canonical result retains `trustState=CANDIDATE_ONLY`: the neighbor rejection
proves the scalar root space is constrained, but does not exhaustively project
that infinite space.  There is no missing producer lineage or composition
gap.

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
