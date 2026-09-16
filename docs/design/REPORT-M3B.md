M3b done. **TIP `3ce5fd92b`** on `refactor/d3-compose2` (merged staging `48f50b540` first — fast-forward, no conflict). Suite **52 @Test, green**; tree clean; composer smokes unchanged (real `paths=0 BLOCKED gaps=15`, probe `paths=1 families=2 solverRuns=2`).

# REPORT-M3B — the explore stage, on the rulings

## 1. Ruling 1 — replacement is an absence (`SlotTable.contextChanged`, `:309-355`)

A replacement is now: a replay that **did not run** the closure's occurrence **and did** run the same code point (node + regionId + execution index) under another context. Two occurrences of one code point that a replay ran **both** are growth (R-I6). The check is per session (`session.activations()` is the authority on what a replay ran); the gap it raises now carries that session's id and says which of the two things happened.

That alone turned the wave around: `replaced` was true on 17897 solely because the recording's **two client checksum requests** (`Anchor:262e8823…`, `Anchor:1b8a6fdf…`) are two occurrences of one code point by construction — under IDENTITY-V3 every concurrent request of one entry point is.

Endpoint replacement is untouched (same consumer endpoint id, different producer endpoint id → BLOCKING, epoch).

## 2. Ruling 2 — a role is not a region (`SlotTable.unretained`, `:282-310`)

A degraded occurrence's region slot is `ROLE.<ROLE>` (minted at `OccurrenceMinterV2:56`). It names a role, not a region of the static candidate graph, so no retained set can grow to hold it and no epoch can be cut for it. It is now **`LINEAGE_LOST` DIAGNOSTIC** naming the region slot; §8 case 2 stays BLOCKING for a regionId that exists in the static graph and is not retained. On the probe corpus the 5 `ROLE.IPC_HANDLER` activations collapse to **one LINEAGE_LOST row** and nothing forks.

## 3. Ruling 3 — flip queries state container terms

`FlipQuery.render` (`:772-800`) now emits, in order: the comment header, then `SmtLowering.declarationsOnly()` for **every session whose lowering the query's terms are written in** (deduplicated by line — two sessions state the same container model, and the same subterm under the same digest only when it is the same text), then the query's own variables, then the assertions, then `SmtLowering.legalSymbols(...)` over the whole — the same spelling pass the composed query gets. Sessions are recorded as terms are lowered (`Builder.lower`, `:283`).

Two new questions the lowering answers so the rename rule stays fail-closed:
- **`SmtLowering.preambleNames()`** (`:986-1035`) — the 54 names the fixed preamble states (`Ref`, `Value` + constructors/selectors, `AssocState`/`IndexedState` + accessors, `assoc_*`/`indexed_*`, `java_int_wrap`, `java_long_wrap`, …), read off the preamble text so the two cannot drift.
- **`SmtLowering.minted(name)`** (`:963-982`) = declared **and not** in `usedSymbols`. A name the lowering invented (`container_dag__`, `identity__`, `environment__`) means what the query says it means; a name that came off a `SymbolExpression` leaf means what the **recording** says, so it is still renamed or refused by name. `SmtText.rewrite` takes a `stated` predicate for exactly this (`SmtText:52-80`).

**The 17897 anchor's own flip now builds and z3 answers it.** Query `$SPN/m4b-probe/solved/obligation_query.smt2`, 12 829 B: 4 comment lines, the composed preamble (3 datatype declarations, 60 `define-fun`, 15 `declare-const`), and one assertion —

```
(assert (not (not (= container_dag__3a6c33dfa10c97b95a64f290 identity__25611ed993))))
```

i.e. the flipped `retrieveDataEncryptionKey#u8#1`: `allKeys.get(wireKeyId) == null`, the fatal arm. **z3: `sat`**, with a model that sets the handoff variables to 0 — `SAT_MODEL_READY`.

**But the model rests on free constants, and the query now says so.** The handoff symbols (`M_I_field_HOFF.…$HandoffLeafCarrier`, 5 of them) are declared by the rendered preamble and appear only **inside** the shared `container_dag__` define-funs; the query's symbol closure walks the assertion text, so `handoff(attach)` never fires for them — no arm, no `Control`, and the obligation carries **0 answers**. I added a DIAGNOSTIC that names each one ("the query declares this recorded symbol and binds it to nothing: it is inside a shared subterm the assertions never name, so no family constrains it"), 5 rows on this query. **This is the next explore design item**: the closure must be driven by the symbols the lowering *used* for a term, not by the tokens visible in its text — which means renaming inside the rendered declarations, and that needs a ruling on `container_dag__` naming (its mint identity is sort+text with no scope, so two sessions can share one name while renaming its leaves differently). I did not start it.

## 4. Ruling 4 — the domain reader (`ExploreCodec.readDomain`, `:122-146`)

Reads both spellings: the case file's `{sourceId, declaredDomainMin, declaredDomainMax}` and the manifest's `{rootId, kind, recordedValue, min, max}`. `ExploreMain --root-domains experiments/hadoop/hdfs-17897/root-domains.jsonl` no longer throws (it did, at `ExploreCodec:127`). Added `Corpus.declaredDomain(rootId)`.

Empty `recordedValue` with a declared relative window is now **`UNSTATED_VALUE` DIAGNOSTIC by the root's name** (`FlipQuery:331-348`): "the case declares a window relative to what this replay read and the mint row states no reading, so the root is neither enumerated nor pinned" — instead of the false "root has no declared domain". That is 17897's `HDFS.BLOCK_KEY.SERIAL_NO` (`recordedValue: ""`).

## 5. The wave on `$SPN/m4b-probe/iter`

```
state=OBLIGATIONS_PROPOSED  wave=0  tasks=14  proposed=13  answered=0
skeleton: slots 78, filled 78, outsideTheClosure 75, replaced=false
gaps: ADMISSION_GAP 84 (DIAG), TOPOLOGY_DIVERGENCE 75 (DIAG), LINEAGE_LOST 1 (DIAG)  — no BLOCKING row
```
(was: `state=TOPOLOGY_DIVERGENCE`, `replaced=true`, **0 obligations**, 2 BLOCKING rows.)

All 13 solved through `ObligationSolverMain` (z3 4.8.12):

| verdict | n | flips |
|---|---|---|
| **SAT_MODEL_READY** | **3** | `retrieveDataEncryptionKey#u8#1` → flipped **false** (×2, one per anchor request: `get(id) == null`, the fatal arm); `addKeys#u19#1` → flipped true |
| UNSAT | 8 | `addKeys#u19#2..5`, `addKeys#u21#1..4` — no world of this corpus takes the other arm |
| NOT_ADMITTED | 2 | `removeExpiredKeys#u15#1..2` — **refused by name** |

Every obligation carries `rootAssignments {}`, `answers {}`, `unproducible []`, `controls 0` — no root or handoff is *bound* by any of these queries, for the two reasons in §3 (free handoff constants) and §6 (no root symbol reaches any predicate).

**The two refusals are the runtime's symbol-spelling mismatch, named not worked around:**
> the flipped predicate names `M_J_field_REGION.ba3902cd-9721-3876-bd7c-d4f7d2fc0284.in.31bcf38c-9bde-3d1f-86f0-641e490dcf6c.occ.207408b6397a59508bab77a963468ff896c22b38fa5ea9eb4e9caccb619fc060_java/lang/Long`, which no mint, attach or read of `seed-result-7133262e` declares

Expressions spell a region input `M_<J>_field_REGION.<r>.in.<uuid>.occ.<hash>_java/lang/Long`; rows spell it `REGION.<r>.in.<uuid>`. Zero of the 46 root symbols and zero of the 175 read symbols occur in any lowered decision term. The runtime agent is fixing it.

Progression across the three rounds on this corpus: queries that build 0 → 5 (M4C) → **11 of 13** (now).

## 6. What I did NOT do

1. Did not rename recorded symbols inside the rendered declarations (§3) — it needs a `container_dag__` scoping ruling first; the hole is named in 5 DIAGNOSTIC rows instead of being silent.
2. Did not touch the runtime, the contract, or the composer's rules; the two `SmtLowering` additions (`minted`, `preambleNames`) are queries, not policy, and the composer's behaviour is bit-identical (both smokes re-run).
3. Did not change `ObligationFactory`, `ClosurePlanner`, the frontier, or the epoch loop.
4. Did not work around the symbol-spelling mismatch (§5) or the `BlockKey#32` read row that still blocks the real corpus (REPORT-M4B §4.1 — unchanged, `1 paths reached the anchor and all were refused`).
5. No new @Test (52); the two rulings fold into `closureHoldsTheWriterOfAReadVersionAndTheWireProducer` — growth vs. absence, and the `ROLE.` pseudo-region — and the EXPR-reference check stays in `nestedGuardChainDeepensOneDecisionPerWave`.
6. No campaign; no `/opt/GraphChecker` or `/opt/hadoop-*`; nothing written into `$SPN/d-runtime/`.
