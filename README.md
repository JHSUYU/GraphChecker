# GraphChecker

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
| Seed campaigns | **7 / 10** (was 4/10) |
| Witnesses in accepted summaries | **16** (was 8) |
| Oracle rank | **1** — passing |
| Encoding faithfulness | proven: forcing the removal branch, the control `expiryDate > now` is **UNSAT** |
| `keyId` binding | proven load-bearing by Z3 ablation — delete the one line carrying the shared-state edge and the query flips to `sat` |
| NN in the plan | yes — 5 of 10 rows are NameNode |
| **NN in a `.smt`** | **no — the pipeline has never reached compose since NN entered** |

The last row is the important one. A run dies if *any* seed campaign fails, so
flip closure, compose and Z3 have not been exercised against the NN-bearing
model even once. Undoing that is queued first (#29) because untested stages hide
defects — this project has already paid for that lesson three times over.

`expiryDate` remains 7 free existential roots on the DN side: A2's projection
reaches the singleton spine `currentKey`, not the `allKeys[]` elements the fatal
read walks. That is the same gap Ruling L named, one hop further along.

---

## Queue

Ordered by what falsifies the report first, then by what binds the query.

**#29 — Seeding failure should be a named gap, not the end of the run.** One
unseeded producer kills everything downstream. The project's own rule already
says otherwise for flips: *a gap is charged to itself; it does not fail the
run*. A producer that cannot be seeded leaves its output port unconstrained —
which is exactly the freedom the acceptance criteria demand be named. Target
failure must still be fatal; there is no query without a target.

**#24 — A bound must not become an event in the workload.** `LoopBoundCut` is
thrown, escapes the region, arrives at the DataNode as a `RemoteException` and
fails a live heartbeat. Escape measured 1:1 across three runs (263/263,
511/511, 277/277). The fix is global and needs no notion of a re-entrant
service root: drop the `throw`, keep the `finish` — the cut is the analysis's
own object, nothing in the program throws it and nothing must survive it, and
`finish` already disables every hook. The bound still bites; the program stops
noticing. Cover `ReplayLoopResourceCut` and the three failure-state cuts in the
same change, and name the abandonment.

**#28 — Two different judgements, currently conflated.** A guard that does not
dominate the demanded output should be demoted but **stay in the identity** (the
path really is different); a guard whose predicate no region input can reach
should **leave the identity** and become an entry assumption (pinning it makes
admission a lottery). Measured: the dataflow-reachability criterion alone does
*not* separate them here — 18 of 20 branches are reachable, and all three
rejecting sites are among them, because the environment enters *through* the
input ports. `60b9f179` addressed the first half at the port instead: a trusted
RPC's whole-reply port is a carrier, not a demanded value, when the same goal
demands a declared projection of that flow. Effect not yet measured end to end.

**#19 + #17 — One recorder package and the timeline it feeds.** The recorder
must state the object identity of a container's members. Then A2's
identity-based pairing extends element-wise with no positional assumption, and
three named gaps close at once (`ABSENT_EXPRESSION`, the two codec gaps). The
counts that look like a pairing puzzle (8 rebuilt against 9 defined; 6 against
3) are almost certainly the wrong denominator — the elements' real producer is
the roll thread, not the RPC handler's activation — which is why #17's timeline
and this belong to one design. #17 itself is composition-layer only: writers on
one lane become a chain of the already-proven summary, alpha-renamed per step,
under a **third ledger** (state-chain bound) distinct from the unroll bound and
the replay cap, and visible in the SMT so a witness can say "within N rolls".

**#21 — Rank targets by residual freedom.** `TargetRank` prefers producer
count, which chose the write-phase handshake over the balancer one and dropped
the presenting chain entirely. Rank by how few unconstrained operands the
closure leaves on the fatal condition — the acceptance criterion itself, so
ranking and witness strength cannot disagree. Pre-verified: the balancer
activation is intact at the instance and plan layers, and DN2's protocol
exchange windows are already marked, so the closure walk should reach the NN
handlers on re-ranking; if it does not, that is a new defect, not a reason to
hand-pick a target.

**#27 — Make declared transports opaque to the VM.** The cross-process relation
is already supplied by declaration and the codec is never analysed, yet the VM
still symbolically executes protobuf encode/decode inside the region. Those
expressions are then replaced wholesale by the declared edge. This is where the
138 MB expression tree comes from, and why `keyId` and a field riding in the
same encoded string have byte-identical reachable sets — the blocker under R1.
The VM must not read protocol config: the planner publishes generic
`opaqueExtents` (method ranges to run concretely, publishing no expressions and
recording no symbolic guards). Fail closed if a demanded endpoint or an
`EXPLORE` guard falls inside one.

**#5 — The 25-minute discovery tax.** Every `RuntimeWorkflowDiscovery` JVM
re-parses the 150 MB region plan, and the cache is keyed on the jar's identity,
so every rebuild costs it again. The 150 MB is honest — 27 rows, 124
activations, 181 goals, no duplication, dominated by inlined evidence — and the
replay JVMs never read it (they get 31 KB–932 KB task plans). The fix is an
index written alongside the plan, not a smaller plan. Evidence has machine
consumers (the dropped-edge audit, the degeneracy gate); moving it behind an
index is right, deleting it is not.

**#26 — Planning-time port capability check, and a per-operand pin probe.**
Both are instances of a doctrine the bug pattern kept rediscovering: what needs
no runtime evidence should be decided at planning time.

**#12 — R1b, after paths close.** Post-closure the predicate set is complete for
the closed path set, so a leaf no recorded predicate reads may demote to
concrete *for composition only*.

**#14** — condense the test suite to roughly 40. **#9 (T5)** — the realizability
loop exists as a tool (`experiments/hdfs/hdfs-11741/smt_realizability_refine.py`
plus `environment-axioms.smt2`); re-run its axioms once `expiryDate` has a real
producer, at which point clock monotonicity becomes instantiable for the first
time.

### Open, not attributed

- `5a5e3738` aborts in glibc with `free(): invalid next size (fast)` and no
  `hs_err`. The shadow-slot use-after-free above it is fixed and its SIGSEGV is
  gone; whether this is an older defect that was masked or something newly
  exposed is **not proven**. Strongest unverified lead: `detach_tmp_exp` indexes
  the temporary-expression store with a slot's stale `index`, and a reset entry
  carries `-1`. Turn it into a named failure before chasing it.
- `b43888a9` publishes an empty summary with 2973 path-condition entries and
  `pathConditionPauseDepth: 1`. It is **not** an instance of #24 — it produced a
  complete result, its log has no resource-cut hits, and a sibling campaign
  walks the same loop in four bodies.
- A DataNode flip replay ends under SIGKILL before publishing, with peak RSS
  961 MB against 182 GB. Skips now carry their kind, so the next occurrence is
  attributable.

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
