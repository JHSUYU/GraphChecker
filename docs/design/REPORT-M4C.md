M4c done. **TIP `850ff2ea8`** on `refactor/d3-compose2` (merged `refactor/flatten-handoff-next` first — fast-forward, no conflict; the merge base was `0251b30ac`, which already contains my M4b commit). Suite **52 @Test, green**; tree clean.

# REPORT-M4C — the container read, and the flip query's references

## 1. §4.2 resolved — what it really was

Not a boxing gap: **`guardedReadTerm` discarded the projection.** The chain:

`allKeys.put(serial, it.next().getValue())` → `ContainerSmtCodec.term` VALUE (`:719-730`) → `associativeEntryValue` (`:1096`) → propagation-wrapper branch (`:1099-1112`), which pushes a scalar projection *inside the read's version arms* (`projectChoice` rebuilds the `ReadFromExpression` with `observedVersion.expression` replaced, `:1686-1700`) → `host.box(selected)` (`:1109`). But `SmtLowering.guardedReadTerm` ignored the node's own arms and re-joined to the session write log by (location, version), handing back the **whole map state** — for which `Value` has no constructor, hence `CannotBox:L`, hence `ContainerRelation:VALUE`. Evidence (refusal detail now carries it): `a container cell declared "L" lowered to MAP: (assoc_put container_dag__f008… container_dag__0399… container_dag__db64…)`, trace `associativeEntryValue:1109 term:726`.

The same discard is why φ compared a map with null: the fatal read's node is `MAP_STATE/77#-3` and its inline `observedVersion.expression` is `assoc_read(put-chain, key)` (the value), while the write log holds the `PUT` chain (the state).

**Fix (`SmtLowering.guardedReadTerm`, `:679-700`, +`observedVersionExpression` `:1306`):** a read is lowered from the expression the VM published **on the node** for the version it observed — that IS the state join, already carrying whatever the read projected out of that version; the write log is the fallback for a node that states only a version id; then the concrete pin; then `UNSTATED_VALUE`. Same version, same session, one step further along. This is the ruling's "an associative entry whose value is a reference is an opaque object reference, never boxed as a state" — a read of a reference cell no longer returns a state at all. All 732 `ReadFromExpression` nodes in the corpus carry an inline expression; the synthetic test fixtures carry none and take the write-log fallback unchanged.

**Size: 30 lines in `SmtLowering.java`, nothing in `ContainerSmtCodec`** (well under the ~150 budget). No semantics added; no map contents synthesized.

φ now lowers clean: `(not (= container_dag__bfe27bb6c058bdea592331f7 identity__25611ed993))` — `allKeys.get(id) != null`, no refusals.

## 2. ComposeMain — real corpus and probe

```
REAL   $SPN/d-runtime/seed/17897/.../iteration-0000
M4B    paths=0 families=0 roots=46 valuations=1 solverRuns=0 claim=NO_SUPPORTED_WITNESS BLOCKED gaps=27
M4C    paths=0 families=0 roots=46 valuations=1 solverRuns=0 claim=NO_SUPPORTED_WITNESS BLOCKED gaps=15

PROBE  $SPN/m4b-probe/iter  (the two anchor read rows given the value they state nowhere)
M4C    paths=1 families=2 roots=46 valuations=1 solverRuns=2 claim=NO_SUPPORTED_WITNESS gaps=25
```

| gap | REAL M4B | REAL M4C | PROBE M4C |
|---|---|---|---|
| UNSTATED_VALUE DIAG `CannotBox:L` / `ContainerRelation:VALUE` | 6 + 6 | **0** | **0** |
| UNSTATED_VALUE DIAG `INSTANCE/org/apache/…/BlockKey#32@-1` | 1 | 1 | 0 (supplied) |
| DECLARATION_MISSING DIAG (aliasing owner, Fix 2) | 0 | 0 | 14 |
| TOPOLOGY_DIVERGENCE DIAG (outside the closure) | 13 | 13 | 11 |
| ADMISSION_GAP **BLOCKING** | 1 | 1 | **0** |

PROBE: `finalStatus FINAL_READY`, `symbolicPropagationComplete true`, **zero `unsupported__` free constants** in `candidate.smt2`, 2 solver runs.

**z3 verdict at the recorded valuation (ordinal 0): `unsat`**, unsat core `[path_fatal__0, target_path_partition]` → `UNSAT_CLOSED`, `polarityDecides=true`, no BLOCKING gap. That is the right answer and it is meaningful: the seed ran the **healthy** arm (`observedFatal=false`), φ asserts the FATAL arm, so the seed disjunct at its own valuation must be unsat. Claim `NO_SUPPORTED_WITNESS`.

`valuations=1` for two runtime reasons worth recording: the one declared root `HDFS.BLOCK_KEY.SERIAL_NO` has `recordedValue = ""`, so its relative `[+0..+3]` window cannot be resolved; and its symbol `sym__HDFS.BLOCK_KEY.SERIAL_NO__…` occurs **nowhere in the composed artifact** — no declared root reaches the anchor on the seed path, so there is nothing to enumerate. Exploration, not the seed, has to supply that.

## 3. ExploreMain, one wave on `$SPN/m4b-probe/iter`

```
state=TOPOLOGY_DIVERGENCE  wave=0  tasks=14  proposed=0  answered=0
skeleton: slots 78, filled 78, outsideTheClosure 75, replaced=true
gaps: ADMISSION_GAP 84, TOPOLOGY_DIVERGENCE 77   (obligations.jsonl: 0 rows)
```

**0 obligations, and not because of flippability:** `skeleton.replaced` short-circuits the wave (`ExploreMain:140-145` proposes an empty list when a replacement is found). The replacement is `SlotTable.contextChanged` (`:310-330`) firing on the anchor itself:

> `hdfs-17897/dn0#…/REGION.53092d3e…/ctx:Anchor:262e88230660f77e@HDFS_SASL/striped-file-checksum/idx:…` — "the closure holds `Anchor:1b8a6fdf514f4790@HDFS_SASL/striped-file-checksum` at this code point and this replay ran it as `Anchor:262e88230660f77e@…`"

These are the **two client checksum requests** of one recording — two different occurrences at one code point, which R-I6 calls growth, not replacement. The rule keys on (node, region, execution index) and treats a differing CausalContext as a contradiction; under IDENTITY-V3 the context is *part* of the identity, so two concurrent requests always collide there. **M3's rule to rule on** — I did not change it. (Second BLOCKING row, also M3's: `retained set must grow: ROLE.IPC_HANDLER`, §8 case 2.)

With the divergence gate aside (measured directly through `ClosurePlanner` + `ObligationFactory`, probe in `$SPN/m4b-dig`, not in `src/main`):

```
raw-flippable 19 ; lowered-flippable 13 ; queries built 5 ; refused 8
```

- **13 candidates** (6 of the 19 dropped: concrete branches with an empty term — nothing to negate).
- **5 build a query**, all `addKeys#u19#1..5` (`<` / `>=` over constants), each `controls=0 rootVariables=[]` — no root or handoff reaches them, so they are flips with nothing to move.
- **8 refused by name**, `DECLARATION_MISSING`, each naming the lowered term the flip query's own vocabulary cannot state:
  - `retrieveDataEncryptionKey#u8#1` (×2, the anchor's own predicate) → `container_dag__bfe27bb6…`, `container_dag__3a6c33df…`
  - `addKeys#u21#1..4` → `container_dag__24b56868…`, `identity__353c374815`, `identity__871f36081b`, `identity__31d562487e`
  - `removeExpiredKeys#u15#1..2` → `M_J_field_REGION.ba3902cd….in.31bcf38c….occ.207408b6…_java/lang/Long`

That last name is the substantive finding for the round: **the expression table and the rows spell region inputs differently** — expressions say `M_J_field_REGION.<r>.in.<uuid>.occ.<hash>_java/lang/Long`, rows say `REGION.<r>.in.<uuid>`. Zero of the 46 root symbols and zero of the read symbols occur in any lowered decision term. Until those agree, no flip can bind a root and no witness can move one — and it is also why M4B's Fix-3 placeholder rule counts 0. Runtime's.

The flip query also has no container preamble (`FlipQuery.render`, `:756-782`, declares only Int/Bool/Real): a predicate that lowers to `assoc_*`/`Value` terms cannot be stated there at all. It now refuses by name rather than emitting an unparseable query. Giving it `SmtLowering.declarationsOnly()` plus the lowering's declarations is the next explore step; it needs a ruling on cross-session naming first (two sessions' `container_dag__` names are digests of text, and two sessions' texts can coincide), so I did not start it.

## 4. Other changes in this commit

- **`ExploreCodec.EXPLORATION = "exploration"`** and the four stage-raised `GapRow.of("", …)` sites (`SlotTable:323`, `ExploreMain:212`, `ClosurePlanner:94`, `ObligationSolverMain:97`). `GapRow` requires a session id, so **every one of those rows threw where it was raised** — the first divergence a wave found killed the wave instead of being reported by it. That crash is what blocked item 3 (stack: `Fields.text → GapRow.of → SlotTable.contextChanged`). The composer already names its own gaps "composition"; this is the same rule.
- **`FlipQuery.statedTerm`** (`:152`) — the ONE lowering, used at `flippable` (`:122`), the prefix/flipped conjunct (`:283`), a family arm's prefix (`:435`), a delivery's prefix (`:620`). A term with no reference comes back unchanged.
- **`FlipQuery.predicate`** (`:147`) — a concrete branch (empty term) is not flippable and contributes no conjunct; `"(not )"` is not SMT.
- **The `CannotBox` refusal now names the shape it got**, not just the declared type.
- **Test**: folded into the existing `nestedGuardChainDeepensOneDecisionPerWave` (no new @Test) — the first guard's predicate is now published as `EXPR.0000000000000001` (a `SymbolExpression` over the marker) and the existing assertions (1 obligation at `Guard#u8`, SAT, `CASE.MARKER=true`) only pass if the reference was lowered; plus a concrete `Concrete#u3` decision asserted never to be proposed. `Session.symbolic` gained a javaType overload.

## 5. What I did NOT do

1. Did not touch `ContainerSmtCodec` (the fix turned out to be upstream of it) and added no container semantics.
2. Did not change `SlotTable.contextChanged`'s rule (M3's; reported in §3 with evidence) — only the crash it died on.
3. Did not give the flip query a container preamble (§3, needs a cross-session naming ruling).
4. Did not fix `ExploreCodec.readDomain`, which reads `{rootId, kind, recordedValue, min, max}` while the case file `experiments/hadoop/hdfs-17897/root-domains.jsonl` is `{sourceId, declaredDomainMin, declaredDomainMax}` — `ExploreMain --root-domains <case file>` throws (`ExploreCodec:127`). The composer's reader (`ComposeMain:461-467`) accepts both spellings; the explorer's does not. I ran the wave without the flag (it is optional, and the only declared root reaches nothing). One-line alignment, M3's or M5's call.
5. Did not touch the runtime, the contract, `/opt/GraphChecker`, or any `/opt/hadoop-*`; no campaign; no merge; nothing written into `$SPN/d-runtime/`.
6. Did not re-run 17960 (no corpus for it under `$SPN/d-runtime/seed`; 11741's iteration has 0 target rows).

**Still blocking the real 17897 corpus: one runtime row** — `reads.jsonl` seq 9220 at the anchor, `observedVersion=-1` with no `concreteValue` (publisher `runtime/D3RowPublication.java` `fieldAccess` 285-307), exactly as REPORT-M4B §4.1. Nothing composer-side remains in front of it.
