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
of it. Engineering doctrine, build/run recipes and the acceptance criteria live
in [CLAUDE.md](CLAUDE.md) — read that first. This file is the handoff: what the
witness has to look like, where the work stands, and what is queued.

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

Everything below is measured, not estimated.

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

---

## Remaining engineering queue

The semantic HDFS-11741 path is complete. Remaining work is simplification and
cost reduction, not a prerequisite for the current SAT result:

- Project demanded scalar RPC leaves directly at the configured trace boundary,
  then retire `ARRAY_SNAPSHOT` and protobuf/container reconstruction paths.
- Pre-project the few scheduler indices now obtained by repeatedly parsing the
  large runtime region artifact, while retaining the evidence needed by audits.
- Replace remaining non-semantic artifact/closure fingerprints with canonical
  identities where the hash adds no correctness property. RPC value, argument,
  and payload fingerprints are already absent.
- Continue the lean-code audit after each rebuild. Generated stress fixtures and
  case configs are now rebuilt on demand rather than tracked; semantic binding,
  iterator-removal, false-SAT, and process-exit regressions remain as tests.

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
