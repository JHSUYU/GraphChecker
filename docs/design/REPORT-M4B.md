# REPORT-M4B — COMPOSER against the re-recorded 17897 seed

Branch `refactor/d3-compose2`, tip **`69565b5c1`**. Corpus `$SPN/d-runtime/seed/17897/schedule/iteration-0000`, one session `seed-result-7133262e`, 550 rows, 120 expressions.

## 1. The ComposeMain line, before and after (same command, the one in the mandate)

```
BEFORE  paths=0 families=0 roots=46 valuations=1 solverRuns=0 claim=NO_SUPPORTED_WITNESS BLOCKED gaps=17
AFTER   paths=0 families=0 roots=46 valuations=1 solverRuns=0 claim=NO_SUPPORTED_WITNESS BLOCKED gaps=27
```

| gap | before | after | |
|---|---|---|---|
| UNSTATED_VALUE DIAG `…names symbols nothing declares: [EXPR.1f3c6978d870b1bc]` on decision `…retrieveDataEncryptionKey#u8#1` | 1 | **0** | Fix 1 |
| same, on `phi of …` | 1 | **0** | Fix 1 |
| UNSTATED_VALUE DIAG `INSTANCE/org/apache/…/BlockKey#32@-1` | 1 | 1 | runtime row, §4.1 |
| UNSTATED_VALUE DIAG `CannotBox:L` | 0 | 6 | composer, §4.2 (newly *reachable*: φ is now lowered at all) |
| UNSTATED_VALUE DIAG `ContainerRelation:VALUE` | 0 | 6 | same subtree |
| TOPOLOGY_DIVERGENCE DIAG (interaction outside the closure) | 13 | 13 | unchanged |
| ADMISSION_GAP **BLOCKING** | 1 | 1 | text changed (Fix 4) |

```
- "no session of this corpus published a path that reached the declared occurrence"
+ "1 paths reached the anchor and all were refused:
   INSTANCE/org/apache/hadoop/hdfs/security/token/block/BlockKey#32@-1"
```

**Acceptance (2) is met by its second branch:** `paths` is still 0 and §4 names the exact rows/fields and whose they are. Evidence nothing else stands in the way: on a **copy** of the corpus (`$SPN/m4b-probe/iter`) where the blocking read rows are given a value, the composer admitted the path — `paths=1 families=2 roots=46 solverRuns=1` — before §4.2 became reachable.

## 2. What changed and why (file:line at the tip)

**Fix 1 — EXPR refs inside terms.** `SmtLowering.statedTerm(term, origin)` (`SmtLowering.java:244`): every `EXPR.<16 hex>` token of any published term is resolved through the session's `ExpressionTable` and lowered by `dispatch` — the same routine that lowers `ExportRow.expressionRef` — its Java definedness becoming a side condition of the open conjunction; repeats to a fixed point (guard 4); a ref the table does not hold raises `UNSTATED_VALUE:<the ref>`. The table arrives via `begin(session, join, expressions)` (`SmtLowering.java:422`) fed by `CorpusIndex.expressions(sessionId)`. Consumers: π `Composer.java:551`, φ `Composer.java:564`, every family arm's producer prefix `Composer.java:985`.

Four things had to be true for that to be worth anything, and each was wrong:

1. **`begin`/`end` now NEST** (`SmtLowering.java:422,440`, a `Frame` stack). An arm is lowered in its producer's scope *in the middle of* composing a path (`handoffReads`→`pairedArm`→`lower`); the old `begin` overwrote the path's frame, so for the rest of that path `join` was `NO_JOIN` (no read inside φ could join a write), `openRefusals` was null (nothing could refuse) and scope was `""`. Measured before the fix on the probe corpus: **23 free `unsupported__` constants in `candidate.smt2` with an empty `finalStatusRefusals`** — a path admitted on free constants instead of refused by name.
2. **A path's refusals are read BEFORE `end()`** (`Composer.java:576`) — `end()` nulls them and the gap loop ran after it, so it always saw an empty list.
3. **`unknown()` asks `defined()`, not `declared()`** (`SmtLowering.java:983`, `Composer.java:1552`): a named container subterm is a `define-fun`; φ's lowering produces them and the old check refused φ for naming `container_dag__0a3ed66f…`, which the query itself defines.
4. **Names SMT-LIB cannot spell bare are quoted `|…|`** (`SmtLowering.legalSymbols`, `:1149`; applied in `body()`, `declarationsOnly()`, `Solver.ask` `:127,134`; `Solver.unquoted` strips bars off model names). A read symbol is `MAP_STATE/4#-3@v112` and `#` opens a bit-vector literal: z3 answered the whole query `(error "line 32 column 27: invalid bit-vector literal")` — no verdict at all. A spelling, not a rename, so published terms keep meaning what they said.

Also `Composer.predicate(conjunct)` (`:1009`): a CONCRETE branch is published with an empty `term`, which `Arms.conjunct` renders `""` / `"(not )"` — neither is SMT and conjoining them voids the query. Skipped, not refused: with no symbolic value at the site the arm depends on no root, so omitting it is exact (core-design-principle addendum 2026-09-13 22:20). 10 of this corpus's 35 decision rows are that shape.

**Fix 2 — location owners.** `Arms.namedOwner(LocationId)` (`Arms.java:319`), used at `Composer.java:1118`. Alternatives (R-I7.1) only where the owner names the storage across replays: an allocation `Endpoint` id (sha16, optionally `#<m>`), the `preWindow:` form, or — the one reading I added — the class of a **STATIC** field, which owns exactly one cell (IDENTITY-V3 §5). A bare rid or a class on a heap location gets delivery only plus one DIAGNOSTIC `DECLARATION_MISSING` naming the location. The version join is unchanged (LocationId equality + observed version, within one session). On the probe run that is 14 such rows (`MAP/4#-3`, `INSTANCE/63#32`, `INSTANCE/61#40`, `ARRAY/64#1`, `INSTANCE/67#32`, `INSTANCE/65#40`, `ARRAY/64#2`, `INSTANCE/70#32`, `INSTANCE/68#40`, `ARRAY/64#3`, `INSTANCE/73#32`, `INSTANCE/71#40`, `MAP/77#-3`, `INSTANCE/86#40`) and no state family.

**Fix 3 — placeholders vs roots.** `Composer.placeholder(row)` (`:1273`), applied in `domains()` before the pin; lookup `CorpusIndex.readSymbol`. **Count: 0 of the 46 roots.** The rule is idle here because the two spellings do not yet overlap: 51 of 52 root rows carry `REGION.<r>.in.<uuid>` symbols while all 175 read rows carry `INSTANCE_FIELD/…@vN` / `…@concrete` — zero intersection (10 of the 46 root symbols do appear inside `expressions.json` as `SymbolExpression` leaves). It will fire the moment the runtime publishes region inputs as reads under the same symbol.

**Fix 4 — the BLOCKING text.** `Composer.java:405-420`, text above.

## 3. Also-verified (no change)

- **Selector**: `ComposeMain:140` → `d3.plan.SelectorResolution.resolve` (`SelectorResolution.java:57-77`) matches the v1 selector against the SEED session's `ActivationRow`s **in write order** and returns the k-th (k=1). The two anchor activations are rows 29 (`262e88230660f77e`) and 32 (`1b8a6fdf514f4790`); the composition resolved to the first. Correct.
- **Polarity**: π conjunct = `outcome ? term : (not term)` in the one routine `Arms.conjunct` (`Arms.java:609-612`), applied by the consumer.
- **φ** taken from `TargetRow.phiTerm()` as published, only its refs lowered; no negation anywhere on the φ path.

## 4. What still prevents paths ≥ 1

**4.1 RUNTIME — a read row at the anchor states no value.** `sessions/seed-result-7133262e/reads.jsonl`, rows with `seq=9220`, `regionId=REGION.53092d3e-…` (the anchor), `location={INSTANCE, org/apache/hadoop/hdfs/security/token/block/BlockKey, 32}`, `observedVersion=-1`, `symbol=INSTANCE_FIELD/…/BlockKey#32@concrete`, `javaType=I`, **`concreteValue` member absent**. Nothing joins, nothing pins → refuse by name (CONTRACT-SPEC §5). The composer cannot join it either: the owner is a class, which Fix 2 forbids as a join identity.
Publisher: `runtime/D3RowPublication.java` `fieldAccess(…)` lines **285-307** — it publishes `concreteValue` as `optionalString(value.getAsJsonObject(), "_exp")`, empty whenever the recorded value is a structured expression. Two further defects in the same rows: (a) when `_exp` IS present it is the VM spelling `Y_I_119992` / `Y_J_1789434582005`, while every other recorded-value field in the contract is a plain decimal and `JsonText.smtLiteral` reads decimals — so all 10 rows that do carry a value pin nothing either (respelling alone does **not** admit the path: `$SPN/m4b-probe2`, still `paths=0`; respelling **and** supplying the two missing values does: `$SPN/m4b-probe`, `paths=1 families=2`); (b) the same read event `seq 9220` is published once per open occurrence — it appears under 5 regions with one symbol, and that symbol `INSTANCE_FIELD/<class>#<slot>@concrete` is the same string for every instance and every read.

**4.2 COMPOSER — φ names an associative entry value the lowering cannot box.** With 4.1 out of the way the path is refused by `CannotBox:L` ×6 and `ContainerRelation:VALUE` ×6. Node inside `EXPR.1f3c6978d870b1bc` at `/_left/expression/observedVersion/expression/receiver×6/arguments[1]` (and one level up):
`ContainerRelation VALUE ASSOCIATIVE _java_type="L"` ← `NEXT` ← `ITERATOR` ← `ConsumerBoundaryExpression` (which lowers clean, sort MAP) — i.e. `allKeys.put(serialNo, it.next().getValue())`, the NN's `updateKeys` loop. `ContainerSmtCodec.term` KEY/VALUE (`:719-730`) → `associativeEntryValue` (`:1096`) → propagation-wrapper branch (`:1099-1112`) → `host.box(selected)` (`:1109`) receives a container STATE rather than a cell, and `SmtLowering.boxed` (`:898-911`) has no `Value` constructor for one (`Value` has `VRef`, nothing for `AssocState`). The `VALUE_VIEW` projection of a bare-reference type (`_java_type="L"`) does not push inside the put chain. Reproduce: `java -cp $SPN/m4b-dig:<jar> Dig2 <iteration> EXPR.1f3c6978d870b1bc '/_left/expression/observedVersion/expression/receiver/receiver/receiver/receiver/receiver/receiver/arguments[1]'` → `refusals [CannotBox:L, ContainerRelation:VALUE]`. This is the composer's, it is in the SEED φ, so it blocks 17897 whatever the runtime does with 4.1.

## 5. What I did NOT do

1. Did not fix §4.2 (`ContainerSmtCodec` is 2,426 lines and every candidate change there adds semantics to the container model — not one of the four fixes).
2. Did not touch `runtime/`.
3. Did not change any contract type, field, spelling or enum; `GapKind` gained no member (both new rows use the existing `DECLARATION_MISSING`).
4. Did not wire the explorer. `FlipQuery` reads terms via `SmtText.symbols`/`rename` and treats `EXPR.<hex>` as undeclared, so **on this corpus it produces no obligation at all**; the capability is on the object it already holds — `corpus.lowering(sessionId).statedTerm(Arms.conjunct(decision), origin)` at `FlipQuery.java:199` and `:374/:474/:535`. Left to M3 (their file).
5. Did not change `Arms.stateArms`'s signature or its HB rule — only added the static `namedOwner`; no existing call site changed.
6. Did not make the composer read the VM's `Y_<tag>_<n>` literal spelling.
7. Did not relax JOIN/PIN/REFUSE for a read the formula never names (which would also have admitted the path) — CONTRACT-SPEC §5 says refuse.
8. No campaign; no touch of `/opt/GraphChecker` or any `/opt/hadoop-*`; no merge.
9. Did not write into `$SPN/d-runtime/` — mutated corpora are copies at `$SPN/m4b-probe/iter` and `$SPN/m4b-probe2/iter`.

## 6. Files (main 5, test 1) — `git show --stat 69565b5c1`

```
d3/compose/Composer.java      166 +   Fix 1-4 consumers, prefix(), predicate(), namedOwner gate
d3/compose/SmtLowering.java   282 +   statedTerm, nesting frames, defined(), legalSymbols
d3/compose/CorpusIndex.java    21 +   expressions(session), readSymbol(session, symbol)
d3/compose/Solver.java         19 +   legal spelling on the way to z3, bars off model names
d3/smt/Arms.java               49 +   namedOwner (additive only)
test D3ComposerTest.java       39 +/- two STATE fixtures on an allocation owner; the aliasing rule asserted
6 files, 545 insertions(+), 31 deletions(-)
```
