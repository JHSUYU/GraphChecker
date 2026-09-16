# REPORT-M1B — the Design 3 contract package

Branch `refactor/d3-contract-pkg`, worktree `SPN/wt-d3-pkg`, base `9b9961b0a`.
**Tip `0fb76bc23`** — "d3.contract: the Design 3 identity, row, exploration and
composition contract".

Gates: `mvn -o -q -DskipTests package` clean; `mvn -o -q test` 65 tests, 0
failures, 0 errors (61 existing + 4 new; cap 80/100 respected). Nothing outside
the new package is touched — `git status` shows only
`src/main/java/.../d3/` and `src/test/java/.../d3/`, and no existing package has
a dependency on it yet.

## 1. Files (37 main + 1 test, 3 556 lines)

### Identity (CONTRACT-SPEC 1)
| file | lines |
|---|---|
| NodeId.java | 85 |
| Role.java | 26 |
| LineageHop.java | 65 |
| OccurrenceAddress.java | 313 |
| Endpoint.java | 95 |
| InteractionKind.java | 14 |
| Interaction.java | 79 |
| LocationKind.java | 11 |
| LocationId.java | 74 |

### Rows, layout, codec (CONTRACT-SPEC 2)
| file | lines |
|---|---|
| ActivationRow.java | 70 |
| DecisionRow.java | 102 |
| ExportRow.java | 81 |
| AttachRow.java | 119 |
| WriteRow.java | 82 |
| ReadRow.java | 94 |
| RootKind.java | 14 |
| RootMintRow.java | 124 |
| TargetRow.java | 94 |
| GapKind.java | 27 |
| GapClass.java | 11 |
| GapRow.java | 83 |
| ExpressionTable.java | 94 |
| SessionDir.java | 140 |
| RowCodec.java | 426 |

### Exploration (CONTRACT-SPEC 3)
| file | lines |
|---|---|
| Task.java | 77 |
| Obligation.java | 127 |
| Verdict.java | 17 |
| ObligationResult.java | 67 |

### Composition (CONTRACT-SPEC 4)
| file | lines |
|---|---|
| Arm.java | 91 |
| Family.java | 63 |
| PathEntry.java | 74 |
| RootDomain.java | 85 |
| ClaimKind.java | 17 |
| Claim.java | 96 |
| CompositionManifest.java | 103 |

### Internal + test
| file | lines |
|---|---|
| Ids.java (package-private, sha16) | 40 |
| Fields.java (package-private, checks + copies) | 106 |
| src/test/.../D3ContractTest.java (4 @Test) | 269 |

Style, uniformly: plain final classes, private final fields, records-style
getters (`sessionId()`), ONE static `of(...)` per type taking the spec's fields
in the spec's order, `equals`/`hashCode`/`toString`; no Lombok, no second
factory overload, Java 8 throughout.

## 2. Spec ambiguities and how they were resolved

1. **`lineageLost` is not in the render, so it is not in `id()`.** The spec
   renders `node#epochN/hop/.../region/REGION.x#k` and defines `id()` as
   sha16(render), which leaves the degraded flag out of both. Resolved: the flag
   is a property of the evidence, not of the address — it travels in the value
   (`equals`/`hashCode`) and in JSON, but a degraded row and a complete row
   about the same activation have the SAME `id()` and therefore join
   (INTERACTION-ID R-I1: "the interaction still exists and is still keyed by
   both endpoints"). Consequence tested: `parse(render(a))` equals `a` for every
   address with `lineageLost=false`, and the flag survives the row codec.
2. **`Endpoint.id()` composition is unspecified** (only `Interaction.id()` is
   spelled out). Resolved: `sha16(occurrence.id() + "\n" + site + "\n" +
   ordinal + "\n" + attempt)` — separated, because `site` is free text.
   `Interaction.id()` follows the spec literally, `sha16(kind.name() +
   producer.id() + consumer.id())` with no separators, which is unambiguous
   because the two ids are fixed-width 16 hex.
3. **The v1 request spelling's hop ordinal.** The spec writes
   `node#epochN/region/REGION.x@src#epochM/api#k → one hop REQUEST@src/api#k`,
   using `k` for both. Resolved literally: the hop's api is `src/api` verbatim
   (`hdfs-17897/client#epoch0/striped-file-checksum`) and the hop's k is the
   address's k. So the first test string renders as
   `hdfs-17897/dn0#epoch0/REQUEST@hdfs-17897/client#epoch0/striped-file-checksum#1/region/REGION.53092d3e-263d-3a18-b7a5-ae5b437d96de#1`.
   The second test string is byte-identical to the v2 render of an address with
   an empty lineage, so it round-trips unchanged.
4. **Hop boundaries are ambiguous in the grammar** — a node name carries `/`
   (`hdfs-17897/dn0`) and an api carries both `/` and `#`
   (`...client#epoch0/striped-file-checksum`). Resolved with two stated rules:
   the node ends at the first `#epoch<digits>` that `/` or the head's end
   follows; a hop ends at the first `#<digits>` that the string's end or another
   well-formed hop (a KNOWN `Role` name followed by `@` or `#`) follows. Both
   spellings in the mandate and a three-hop v2 address with an api containing
   `/` and `#epoch0` are covered by the test.
5. **`parse` is strict, not total.** v1's `OccurrenceAddress.parse` returned a
   `NONE` that matched nothing; this one throws `IllegalArgumentException`
   naming the string and the reason. Same fail-closed intent, and a new package
   has no legacy caller that needs a sentinel. (If M2/M3 want a soft parse they
   should catch, not re-add `NONE`.)
6. **`NodeId.epoch` is an `int`** per the spec (v1 kept the epoch a String).
   `NodeId.parse` was added because `OccurrenceAddress.parse` needs it and the
   node key is parsed in more than one module.
7. **No JSON shape is given.** Resolved: `occurrence` = `{address, lineageLost}`
   (the render, greppable, plus the flag), `endpoint` =
   `{occurrence, site, ordinal, attempt}`, `location` = `{kind, owner, slot}`;
   every other field is its own member with the Java field's name — `cls` kept
   verbatim on `GapRow`. Rule for absence: a field the spec marks nullable is
   OMITTED when null and reads back null; every other field is always written,
   so a missing member is a malformed row rather than a silent default. No
   derived members (no `id` echo) — one place computes an id.
8. **"one read/write method per row kind" vs. the file layer.** Resolved: the
   per-kind pair is row ↔ `JsonObject`
   (`writeActivation`/`readActivation`, … nine pairs), and the file layer is
   kind-agnostic (`writeJsonl` / `appendJsonl` / `readJsonl`, one object per
   line) with two typed helpers `writeAll(Path, List<T>, Function<T,JsonObject>)`
   and `readAll(Path, Function<JsonObject,T>)`. A missing file reads as no rows,
   so no reader ever needs another kind's file. `expressions.json` has its own
   pair (`writeExpressions`/`readExpressions`).
9. **No codec is specified for the exploration/composition types.** They are
   left as plain Gson-reflective-friendly value classes; only the row kinds and
   the expression table go through `RowCodec`. M3/M4 can add their own file
   helpers without touching the contract.
10. **`RootDomain.min`/`max` are not marked nullable** although
    `RootMintRow.domainMin`/`domainMax` are. Resolved: both nullable, and a root
    with neither bound answers `pinned() == true` — "a root without a domain is
    pinned everywhere" needs one spelling, not two.
11. **Empty vs. null for the strings the spec does not mark nullable.** Resolved:
    they may be empty but never null (`Arm.piRef` is `""` for an unattested arm,
    `ObligationResult.sessionId` is `""` when no replay ran); ids, symbols,
    sites, region ids and session ids must be non-blank. Ordinals (`k`, `ordinal`)
    are 1-based; `attempt`, `epoch`, `valuationOrdinal`, `valuations` are ≥ 0.
12. **`Verdict.VALIDATED` is kept verbatim** even though the owner ruling removed
    the VALIDATE replay stage; the spec lists it, so it stays in the enum with no
    producer in D3.
13. **Additions beyond the literal type list**, each small and stated here:
    package-private `Ids` (the one sha16) and `Fields` (null checks, defensive
    copies); `Endpoint.stateSite(class, method, bci, write)` and
    `LocationId.heapOwner(allocation, m)`, which spell the two formats the spec
    gives only in prose so the runtime and the composer cannot drift;
    `ReadRow.UNKNOWN_VERSION` (-1); derived predicates `AttachRow.interaction()`,
    `Family.anyUnattested()`, `GapRow.blocking()`, `Claim.blocked()`,
    `RootMintRow.pinned()`, `RootDomain.pinned()`; `SessionDir.create()` and
    `SessionDir.sessionsIn(iteration)`; `ExpressionTable.empty()/fromJson/toJson`.
    Nothing named in the spec was renamed, dropped or given a second overload.

## 3. Test (4 @Test, cap-safe)

`D3ContractTest`: (1) both v1 spellings parse, the request spelling becomes one
`REQUEST` hop and renders as v2, the bare spelling renders byte-identically, a
three-hop v2 address with a slashed api round-trips; (2) two producers on the
same port with the same consumer k give two endpoint ids and two interaction
ids, an attempt separates a retry, a STATE edge over the same pair is a third
id, and a degraded producer keeps the interaction's id while answering
`producerDegraded()`; (3) all nine row kinds round-trip through the JSONL line
form, a null nullable comes back null, the degraded flag survives, and the
session layout holds each kind in its own file; (4) a heap location's owner is
`<allocating endpoint id>#<m>` and separates two allocations at one site from a
static field's class owner.

---

# Contract v1.1 — `seq`, `javaType`, `SOLVER_TIMEOUT`

Branch `refactor/d3-contract-pkg`, fast-forwarded onto staging `19b311384`
first (it was a merge of the v1.0 tip, so the merge was empty).
**Tip `6f741ef79`** — "d3.contract v1.1: seq, javaType, SOLVER_TIMEOUT".
`mvn -o -q -DskipTests package` clean, `mvn -o -q test` 65 tests / 0 failures
(still 4 @Test in `D3ContractTest`; no new test method).

What changed, and nothing else:

1. **`long seq`** — the session-monotonic event sequence number — on
   `DecisionRow`, `ExportRow`, `AttachRow`, `WriteRow`, `ReadRow` and
   `TargetRow`. Refused below 0 (`Fields.sequence`), part of `equals`/`hashCode`
   and of `toString` (rendered `<sessionId>#<seq>`). Not on `ActivationRow`,
   `RootMintRow` or `GapRow`, which the coordinator did not list.
2. **`String javaType`** — the JVM descriptor (`I`, `J`, `Z`,
   `Ljava/lang/String;`) — on `ExportRow`, `AttachRow`, `ReadRow` and
   `WriteRow`. Required non-blank; validated as text only, NOT parsed as a
   descriptor (a contract that half-validated a descriptor would be a second
   opinion about sorts, which is the thing the field exists to remove).
3. **`GapKind.SOLVER_TIMEOUT`** — "the solver gave no answer in the time it was
   given" — appended after `LINEAGE_LOST`.

**Factory parameter order** (the one ambiguity here — the coordinator gave the
fields, not their position): `seq` goes immediately after `sessionId`, so a row
always opens with where it is (`session`, `seq`); `javaType` goes immediately
after the thing it gives a sort to (`expressionRef` on export and write,
`symbol` on attach and read). In full:

```java
DecisionRow.of(sessionId, seq, occurrence, siteId, ordinal, outcome, term, clockReadings)
ExportRow.of  (sessionId, seq, endpoint, expressionRef, javaType, handle, recordedValue)
AttachRow.of  (sessionId, seq, endpoint, symbol, javaType, arrival, answered,
               answeredValue, producer, correlationId)
WriteRow.of   (sessionId, seq, endpoint, location, version, expressionRef, javaType)
ReadRow.of    (sessionId, seq, endpoint, location, observedVersion, symbol, javaType,
               concreteValue)
TargetRow.of  (sessionId, seq, occurrence, anchorSiteId, phiTerm, observedFatal,
               reachedAnchor)
```

## JSON field names (as `RowCodec` writes them, in write order)

Shared fragments:

| fragment | members |
|---|---|
| occurrence | `address` (the v2 render), `lineageLost` |
| endpoint | `occurrence`, `site`, `ordinal`, `attempt` |
| location | `kind`, `owner`, `slot` |

One file per kind under `<iteration>/sessions/<sessionId>/`, one object per
line. `?` marks a member omitted when the value is null; every other member is
always written.

| file | members |
|---|---|
| `activations.jsonl` | `sessionId`, `occurrence`, `taskId`, `focused`, `instrumented` (v2.3), `threadKey` (v2.3), `startedBy?` (v2.3, endpoint) |
| `decisions.jsonl` | `sessionId`, `seq`, `occurrence`, `siteId`, `ordinal`, `outcome`, `term`, `clockReadings` (object: symbol → long) |
| `exports.jsonl` | `sessionId`, `seq`, `endpoint`, `expressionRef`, `javaType`, `handle`, `recordedValue` |
| `attaches.jsonl` | `sessionId`, `seq`, `endpoint`, `symbol`, `javaType`, `arrival`, `answered`, `answeredValue?`, `producer?` (endpoint), `correlationId` |
| `writes.jsonl` | `sessionId`, `seq`, `endpoint`, `location`, `version`, `expressionRef`, `javaType` |
| `reads.jsonl` | `sessionId`, `seq`, `endpoint`, `location`, `observedVersion`, `symbol`, `javaType`, `concreteValue?` |
| `roots.jsonl` | `sessionId`, `seq` (v1.2), `occurrence`, `rootId`, `symbol`, `kind`, `recordedValue`, `domainMin?`, `domainMax?`, `declared` |
| `targets.jsonl` | `sessionId`, `seq`, `occurrence`, `anchorSiteId`, `phiTerm`, `observedFatal`, `reachedAnchor` |
| `gaps.jsonl` | `sessionId`, `kind`, `cls`, `subject`, `detail` |
| `expressions.json` | one object, `ref` → the VM's `EXPR.v1.*` expression, unchanged |

The round-trip test now carries a session order (export 4, attach 9/11, write
10, decision 12, read 14, target 15), asserts `seq` and `javaType` survive the
line form, and round-trips a `SOLVER_TIMEOUT` gap.

---

# Contract v1.2 — `seq` on RootMintRow

Merged staging `6d47ed98f` first (fast-forward; d3.compose had been built on
v1.1 and the contract package was untouched there).
**Tip `df98d0731`** — "d3.contract v1.2: seq on RootMintRow".
`mvn -o -q -DskipTests package` clean, `mvn -o -q test` 71 tests / 0 failures
(the merge brought d3.compose's tests in; `D3ContractTest` is still 4 @Test).

`RootMintRow.of(sessionId, seq, occurrence, rootId, symbol, kind,
recordedValue, domainMin, domainMax, declared)` — `seq` immediately after
`sessionId`, refused below 0 (`Fields.sequence`), in `equals`/`hashCode`, and
rendered `<sessionId>#<seq>`. `roots.jsonl` gains the `seq` member in the same
position (table above updated); `RowCodec.writeRootMint` writes it always and
`readRootMint` requires it.

One call site outside the package had to move with the signature:
`D3ComposerTest`'s session builder (`marker(...)`) now passes `++seq` like its
sibling row builders — the same one-token change its `export`, `attach`,
`decision` and `target` builders already carried from v1.1. No src/main code
outside d3/contract constructs a `RootMintRow`, so nothing else moved.

---

# Contract v2.0 — causal execution index identity

Merged staging `refactor/d3-contract` (`7b5fa15f7`) first — clean, no conflicts.
**Tip `40c5ae839`** — "d3.contract v2.0: causal execution index identity".
Implements IDENTITY-V3 with IDENTITY-IMPL §A as the binding shape, plus §5
(Memory Indexing) for `LocationId`.

## Build state (read this before merging)

- `src/main` compiles: `mvn -o -DskipTests package` reports **zero** main-source
  errors.
- `d3.contract` itself is verified green in isolation — compiled with javac
  against the maven test classpath and run under JUnitCore: **4 tests, OK**.
- `mvn test` does NOT run yet: two test classes owned by other agents still
  construct endpoints with the v1.x `int ordinal` —
  `d3/compose/D3ComposerTest.java` (28 errors) and
  `d3/explore/D3ExploreTest.java` (18 errors). The mechanical fix is one shape:
  `Endpoint.of(occ, site, <int n>, attempt)` becomes
  `Endpoint.of(occ, site, ExecutionIndex.of(Arrays.asList(Frame.of("<fixture
  call site>", 0))), attempt)`; one `RootMintRow.of` in D3ExploreTest takes the
  v1.2 `seq` it never got. I left both files to M3/M4 as instructed rather than
  editing fixtures whose assertions I cannot judge.
- The only file outside `d3/contract` I did touch is `d3/explore/FlipQuery.java`,
  two lines: the removal of `Endpoint.ordinal()` broke two solver NAME HINTS
  (`"vH_" + site + "_" + ordinal`), now `siteIndex().hash()`. The identity those
  names hang off — the interaction id and the endpoint id used as the map key —
  is untouched, so no behaviour moves.

## The types (41 files in the package: 4 new, 1 deleted, 4 rewritten)

| file | lines | what |
|---|---|---|
| Frame.java (new) | 86 | `callSite` (class#method#bci) + `iteration`; render `callSite@iter`; a call site may carry neither `/` nor `@`, so the canonical render parses back exactly |
| ExecutionIndex.java (new) | 121 | frames + the 16-hex fold `fold(h,f) = sha16(h + "/" + callSite + "@" + iteration)`, seeded at `sha16("")`; `push(Frame)` is the runtime's incremental step; render `f/f/f` |
| CausalContext.java (new) | 231 | sealed by a private constructor; `Anchor(producerEndpointId, rpcSite)`, `Root(role, windowIndex)`, `Lost(role)`; `of(...)` overloads pick the form; renders `Anchor:<id>@<site>`, `Root:<ROLE>#<w>`, `Lost:<ROLE>` |
| Selector.java (new) | 91 | `(regionId, api?, k)` + `matches(occurrence, rpcSiteApi)` |
| OccurrenceAddress.java | 188 | `(node, regionId, context, index)`; `render()`, `parse()`, `parseSelector()`, `id()`, derived `lineageLost()` |
| Endpoint.java | 117 | `(occurrence, site, siteIndex, attempt)`; `stateSite`, `allocationSite`, `render()`, `id()` |
| LocationId.java | 105 | `allocated(...)`, `preWindowOwner(...)`, `preWindow()` |
| LineageHop.java | −65 | deleted with the lineage list |
| RowCodec.java | 523 | occurrence/context/index/endpoint codecs |
| D3ContractTest.java | 329 | 4 @Test |

Ids, exactly as IDENTITY-IMPL §A composes them:

```
occurrence.id  = sha16(node.render + "/" + regionId + "/" + ctx.render + "/" + idx.hash)
endpoint.id    = sha16(occ.id + "/" + site + "/" + siteIdx.hash + "/" + attempt)
interaction.id = sha16(kind.name() + producer.id + consumer.id)      (unchanged)
```

Canonical renders (people, reports, refusals — not the row format):

```
occurrence  node#epochN/region/REGION.x/ctx:<context>/idx:<callSite@iter>/<callSite@iter>
endpoint    <occurrence>/site:<site>/sidx:<callSite@iter>/.../att:<attempt>
context     Anchor:<producerEndpointId>@<rpcSite> | Root:<ROLE>#<w> | Lost:<ROLE>
```

## JSON shapes (v2.0)

An occurrence is written as its parts, not as a rendered string: a row that
carries the parts needs no parser to be read by anything else, and the
degradation is the context's own form rather than a flag beside it. The
`lineageLost` member is GONE from every row.

| fragment | shape |
|---|---|
| occurrence | `{"node": "hdfs-17897/dn0#epoch0", "regionId": "REGION.x", "context": {…}, "index": [frame, …]}` |
| context (anchor) | `{"form": "ANCHOR", "producerEndpointId": "9f2c1a3b4c5d6e7f", "rpcSite": "ClientNamenodeProtocol#getBlockKeys"}` |
| context (root) | `{"form": "ROOT", "role": "KEY_MANAGER_TICK", "windowIndex": 3}` |
| context (lost) | `{"form": "LOST", "role": "UNKNOWN"}` |
| index / siteIndex | `[{"callSite": "o.a.h.h.s.d.DataXceiver#run#12", "iteration": 0}, …]` (outermost first; `[]` when empty) |
| endpoint | `{"occurrence": {…}, "site": "XCH.…", "siteIndex": [frame, …], "attempt": 0}` |
| location | `{"kind": "INSTANCE", "owner": "<allocating endpoint id>", "slot": "expiryDate"}` — owner is the class for STATIC and `preWindow:<class>#<m>` for a pre-window object |

Row members are otherwise unchanged (v1.1/v1.2 tables above still hold).

## Choices I had to make

1. **`lineageLost` is not a field.** The first brief listed it as a fifth
   component; IDENTITY-IMPL §A — which the coordinator made binding — does not,
   because `Lost(role)` states it. Resolved: no field; `lineageLost()` stays as
   a derived reading of the context, so `Interaction.producerDegraded()`, the
   gap kind and every caller keep working, and the degradation is now INSIDE the
   id instead of beside it (a degraded row and a complete row about one
   activation no longer collide — they are different contexts, which is right:
   a lost scope is not the same causal fact as a known one).
2. **Accessors are `context()` and `index()`** (the first brief's field names);
   §A abbreviates them `ctx`/`idx`. JSON follows the accessors.
3. **Frame's field is `callSite`** per §A (the brief said `callSiteId`).
4. **The fold's seed** is unstated in §A; it is `sha16("")`, so an index with no
   frames still has a 16-hex hash and `ExecutionIndex.empty()` is a usable
   identity rather than a hole.
5. **`Selector` keeps the v1 node prefix** (v2.1 -- see below). v2.0 dropped it
   per §A's `(regionId, api, k)`; the coordinator accepted the flag and the node
   is now a fourth, optional component.
6. **`Selector.matches` takes the api as a parameter.** The contract does not
   know how a deployment spells an RPC static site, so it will not guess the api
   out of `rpcSite`; the caller extracts it. A selector that names an api
   matches nothing that no message started.
7. **`LocationId.allocated` refuses `STATIC`** — a static field is owned by its
   class, and an owner that said otherwise would join two different storages.
8. **`parse` stays strict** (throws, naming the string and the reason) for
   addresses, contexts, frames and indexes.
9. **Separator discipline, so every render parses back**: a region id and a call
   site carry no `/`, a call site no `@`, a producer endpoint id no `@`. An
   `rpcSite` may contain anything but the literal `/idx:` (the address parser
   takes the LAST one).

---

# Contract v2.1 — the Selector carries the node

**Tip `f59b5ff49`** — "d3.contract v2.1: Selector carries the node".
`src/main` compiles (zero main-source errors); `d3.contract` compiled and run in
isolation: **4 tests, OK**. `mvn test` still waits on the two fixture files
D3ComposerTest / D3ExploreTest (unchanged from the v2.0 note above). Nothing
outside `Selector`, `OccurrenceAddress.parseSelector` and the test moved.

`Selector.of(String regionId, String api, int k, NodeId node)` — the node is the
fourth component and may be null:

- `OccurrenceAddress.parseSelector` fills it from the v1 spelling's
  `node#epochN` prefix (both spellings), and accepts a declaration written
  without one (a string that begins at `/region/`).
- `matches(occurrence, rpcSiteApi)` requires `node` to equal the occurrence's
  when it is present; a selector without a node selects on every component.
- `render()` spells the whole v1 form again —
  `node#epochN/region/REGION.x[@api]#k`, or `/region/REGION.x[@api]#k` with no
  node — so a selector round-trips through its own rendering either way.
- `equals`/`hashCode` include the node: two declarations that differ only in the
  component are two selectors.

Why it matters, in one line: two components of one seed session can run the same
region, and the k-th match would otherwise be resolved on the wrong node.

---

# Contract v2.2 — STATE_PAIRING_FLIPPED

Merged staging `59fa99aa5` first (it carries M3's and M4's identity-v3
adaptations).
**Tip `885da8f50`** — "d3.contract v2.2: STATE_PAIRING_FLIPPED".

**The tree is green again**: `mvn -o -q -DskipTests package` BUILD SUCCESS and
`mvn -o -q test` **80 tests, 0 failures, 0 errors** (48 @Test methods, cap 80 /
100). The two fixture files the v2.0 note listed as red — D3ComposerTest and
D3ExploreTest — were adapted by their own agents and came in with the merge.

One constant, placed next to the message kind it mirrors:

```java
/** The recorded roots suffice once the STATE pairing changes. */
STATE_PAIRING_FLIPPED,
```

A witness that reaches the fatal arm with every declared root at its recorded
value, because the shared-field read is delivered by a different eligible,
attested writer than the one the reader observed. Same polarity rule as
MESSAGE_PAIRING_FLIPPED: the seed disjunct must be unsat at the recorded
valuation, or the formula was satisfiable all along and explains nothing.

No codec or test change was needed, and the report's field tables are unchanged:
nothing in `d3/contract` serializes a `ClaimKind` (`RowCodec` covers the nine row
kinds; `GapKind` and `RootKind` are the only enums it writes), the claim travels
in the composer's manifest, which writes the constant's `name()`, and no switch
over the enum is exhaustive — the four call sites in `ClaimPolicy` and
`ComposeMain` compare constants.

---

# Contract v2.3 — instrumented, threadKey, startedBy on ActivationRow

Merged staging `e507f365c` first (clean).
**Tip `f5c29c7ab`**, merged into staging as `d21f45aee` — "d3.contract v2.3:
instrumented, threadKey, startedBy on ActivationRow". M3's `startedBy`
clarification follows it as its own commit, **`117abb839`** ("d3.contract:
startedBy is the thread-creation edge only", javadoc only), on top of
`d21f45aee` — a fast-forward for staging.

**Process note (my error, recorded so it is not repeated):** I first put that
clarification in by amending `f5c29c7ab`, which staging had already merged, and
the two histories diverged. The rule from here: a tip I have reported is
immutable -- no amend, no rebase; every further change is a new commit on top of
it, and branches only move forward. `mvn -o -q -DskipTests package` BUILD SUCCESS; `mvn -o -q test`
**95 tests, 0 failures, 0 errors** (57 @Test methods; `D3ContractTest` still 4,
no new @Test).

```java
ActivationRow.of(sessionId, occurrence, taskId, focused,
                 boolean instrumented, String threadKey, Endpoint startedBy)
```

- `instrumented` — false when the row comes from a lightweight entry hook alone
  (the region is not in the retained/instrumented set, so no decision, export or
  attach row can exist for that occurrence). Required, always written: a reader
  that finds no decisions must be able to tell "never instrumented" from
  "decided nothing".
- `threadKey` — required non-blank, always written; two rows with the same key
  ran in program order.
- `startedBy` — nullable endpoint, omitted from the JSON when null, read back as
  null. It is ONLY the intra-node thread-creation edge: the `Thread.start` or
  executor-submission endpoint whose frame this activation's thread inherited.
  Null for a thread that already existed (a handler pool takes work off a queue)
  and null for an activation a message started -- message causality is the
  occurrence's `CausalContext.Anchor` and stays there. The two are different
  happens-before relations (thread start against message receive) and may both
  hold of one activation without disagreeing; `Arms.ancestor` follows both. The
  javadoc says all of this, because reading `startedBy` as "who caused this
  work" would collapse the two and lose the message edge on every pooled
  handler.

All three take part in `equals`/`hashCode`; `toString` shows the thread and
marks an uninstrumented row.

## JSON keys (activations.jsonl)

`sessionId`, `occurrence`, `taskId`, `focused`, `instrumented`, `threadKey`,
`startedBy?` — the last being the usual endpoint object
(`{"occurrence": {...}, "site": ..., "siteIndex": [...], "attempt": n}`). The
per-file table above is updated. No other row kind changed.

## Call sites I had to move (and what M2 should check)

- `runtime/d3/D3Runtime.java`, the two publication sites:
  `beginActivation` is the instrumented path (`instrumented = true`);
  `ambientActivation` — "an activation that no plan selected", published at the
  first delivery into a region rather than by the region's own entry — is the
  lightweight one (`instrumented = false`). **M2: confirm that reading of
  `ambientActivation`**; it is the one judgement in this change I made from the
  javadoc rather than from a spec line.
- `threadKey()` there is the thread's name plus its JVM id
  (`IPC Server handler 3 on 8020#41`): a name alone repeats across a pool, an id
  alone tells a reader nothing, and both are observations rather than
  invention. Provisional spelling — M2 owns the definitive key.
- `startedBy` is null at both sites: the runtime does not yet carry an endpoint
  on the `Thread.start` / executor arm. That is the honest null, not a
  placeholder to be read as "no starter existed".
- Fixtures in `D3ComposerTest`, `D3ExploreTest` and `D3PlanTest` take the
  mechanical form (`true, "fixture#1", null` / `"main#1"`).
