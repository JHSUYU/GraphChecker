M3c done. **TIP `4c718eefa`** on `refactor/d3-compose2` (merged staging `d8a7e97b9` first — fast-forward, no conflict). Suite **52 @Test green**, shell helper test green, tree clean.

# REPORT-M3C — minted names, the symbol closure, and ADMITTED

## 1. Ruling on minted names (`SmtLowering.name` / `scoped`, `:1000-1035`)

The digest of a shared container subterm is now taken over **sort + the scoped text**: every token of the text that is a recorded symbol (`usedSymbols`) is prefixed with the session scope *for the digest only* — the emitted body is the text as it stands. So a subterm that mentions any recorded symbol gets a per-session name, and two sessions share a name only when the definition is literally the same closed term. Identities and environment cells already carried the scope; this was the one name that did not.

## 2. Ruling on the symbol closure (`FlipQuery.rename` + `SmtLowering.reachedBy`)

`SmtLowering.reachedBy(texts)` (`:1096-1160`) returns **exactly the declarations those texts reach**, dependencies first, walking through the bodies of the subterms they name. `FlipQuery.rename` (`:645-690`) unions the term's visible tokens with that closure, so a handoff inside a shared `define-fun` is renamed and enqueued like any other symbol: `handoff(attach)` fires, the family disjunction is asserted, the `Control` is registered, and the obligation states the answer.

`render` (`:800-840`) now emits: the preamble, **the query's own variables**, then only the reached declarations with their bodies renamed in step, then the assertions. (Variables before definitions: a renamed body names them, and a `define-fun` over an undeclared constant is an error that cascades into every definition above it — that was the first thing z3 said.)

**One more thing had to change for any of it to work:** the name alphabet (`SmtLowering.symbolCharacter`, `:350-366`) was letters, digits, `_ . $` — which splits `M_I_field_HOFF.<sha>_edu/uva/liftlab/…$HandoffLeafCarrier` **at the slash**, so half a name was looked up, no declaration was found for it, and the query emitted a subterm over a constant it never declared (z3: `unknown constant M_I_field_HOFF…`). It is now SMT-LIB's simple-symbol set plus `#` and `'`.

**The refusal** (`UNPRODUCIBLE_ANSWER`, `FlipQuery:889-920`) is worded as the standing rule requires: a recorded symbol the query would declare and bind to nothing means "no family and no pin states it, so **the query is not causally closed** and a model of it would answer with a value the chain does not reach". Nothing about reproducing anything. It fires **0 times** on this corpus — the closure binds everything the terms reach.

## 3. The wave on `$SPN/m4b-probe/iter`

```
state=OBLIGATIONS_PROPOSED  tasks=14  proposed=13  replaced=false
gaps: ADMISSION_GAP 84 (DIAG), TOPOLOGY_DIVERGENCE 75 (DIAG), LINEAGE_LOST 1 (DIAG)
solved: SAT_MODEL_READY 3, UNSAT 8, NOT_ADMITTED 2
```

**The anchor flip, both occurrences** (one per client checksum request) — `retrieveDataEncryptionKey#u8#1`, recorded `true` → flipped **false**, i.e. `allKeys.get(id) == null`:

| | request `Anchor:262e8823…` | request `Anchor:1b8a6fdf…` |
|---|---|---|
| verdict | SAT_MODEL_READY | SAT_MODEL_READY |
| **answers** | `e057288dcf8d2979` → **119992** | `32a61726e2d75e08` → **119994** |
| rootAssignments | `{}` | `{}` |
| unproducible | `[]` | `[]` |
| gaps | none | none |

Both answered attaches are `XCH.da84e470-….req.data-encryption-key-id` **at the anchor occurrence**, and both are backed by an arm from the **client's** export (`SaslDataTransferClient.getUserNameFromEncryptionKey`) — exactly the shape you predicted: one answer per wire handoff the predicate reaches. Before this commit both obligations had `controls 0`, `answers {}`.

The rendered query (19 564 B, `$SPN/m4b-probe/anchor-flip-m3c.smt2`) carries the 6 `vH_…` variables the closure bound, the family arms as disjunctions (`(or (= vH_… 119993) (= vH_… 119992) …)`), the client export's equality (`(= vH_…req vH_…resp)`, `(= vH_…resp 119992)`), and one assertion:

```
(assert (not (not (= container_dag__f27ddde2863e74415b0ff131 identity__25611ed993))))
```

z3: **`sat`**, assigning e.g. `vH_XCH_1174244c…_resp_3 = 119993`.

The other two SAT/UNSAT groups: `addKeys#u19#1` SAT (0 answers — its predicate reaches no wire value), 8 UNSAT, and the 2 `removeExpiredKeys#u15` still `NOT_ADMITTED` for the runtime's symbol-spelling mismatch (`M_J_field_REGION.<r>.in.<uuid>.occ.<hash>_java/lang/Long` in expressions vs `REGION.<r>.in.<uuid>` in rows) — named, not worked around.

**Caveat you should have before reading the SAT.** The VM publishes Java `null` as `SymbolExpression _exp="N"` with an empty `_java_type` (7 occurrences in this corpus, every one the right operand of `!=`; `SYMBOLIC_NULL`, the spelling `SmtLowering.symbolTerm` recognises, never appears). So `N` lowers to an **opaque identity**, not `nullRef`, and `get(id) == null` is satisfiable by making the read return that object. The composer's fuller formula rejects it (probe: `unsat` at the recorded valuation, `UNSAT_CLOSED`) — the explorer proposes, the composed query disposes, which is the pipeline working as designed. But the fatal predicate of all five HDFS cases is a null check, so **`N` → `nullRef` is worth a ruling**; I did not change it, because a wrong guess at the value language silently changes φ on every case. Evidence above; it is the runtime's spelling to confirm.

## 4. `VALIDATED` → `ADMITTED`

Renamed across all of `src` and the shell: `d3.contract.Verdict` (with the reason in its javadoc — "a focused replay exists to COLLECT the arms the seed does not contain; what a flip, a witness or a bug rests on is the composed query and z3's verdict"), `runtime/d3/FocusedReplay:284`, `d3.explore.Frontier` (3 sites), `D3ExploreTest`, `run_engine.sh:1954` (the stamp) and `run_engine_campaign_helpers_test.sh` (its expectation). The shell had to move with it — it writes the verdict string the enum parses — and its test passes (`run engine campaign helper tests passed`). `grep -rn VALIDATED src/ run_engine.sh` → 0.

**No re-run-to-confirm path exists in `ExploreMain` or `ObligationSolverMain`** to delete: the solver builds one query, solves it once, writes `obligation_query.smt2` / `obligation_result.jsonl` / `obligation.jsonl` / `gaps.jsonl` / the replay task plan, and stops; `ExploreMain` never solves. The only replay is the campaign's, and it publishes rows — that is the one whose verdict is now `ADMITTED`.

## 5. Composer unchanged, and what I did not do

Both composer smokes re-run on the final build: real corpus `paths=0 … BLOCKED gaps=15` (still the `BlockKey#32` read row of REPORT-M4B §4.1); probe `paths=1 families=2 solverRuns=2`, z3 `unsat` at the recorded valuation, `UNSAT_CLOSED`, **0 `unsupported__`** in `candidate.smt2`.

Not done: (1) the `N`/`nullRef` question above; (2) the runtime symbol-spelling mismatch; (3) no change to `ObligationFactory`, the frontier, the epoch loop, or any composer rule; (4) no campaign, no `/opt/hadoop-*`, nothing written into `$SPN/d-runtime/`; (5) no new @Test — the closure ruling is folded into `nestedGuardChainDeepensOneDecisionPerWave` (`reachedBy` on the lowered reference must report the recorded leaf `M_MARKER`); the transitive case — a handoff inside a shared `define-fun` — is covered by the corpus evidence in §3 and not by a synthetic container fixture, which I judged not worth the ~60 lines of hand-built container JSON.
