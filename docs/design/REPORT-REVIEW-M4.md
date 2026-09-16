# REPORT-REVIEW-M4 — audit of d3/contract + d3/compose at staging `6d47ed98f`

Read-only. References: REPORT-M1B, REPORT-M4, CONTRACT-SPEC, INTERACTION-ID,
REFACTOR-D3 §0–1. Sizes: `d3/contract` 3,441 lines / 37 files, `d3/compose`
10,106 / 19.

**Summary: the six drift questions come back clean on five and a half. The
composer does not re-derive polarity, does not re-derive pairing, keys arms by
the interaction, guards arms only by the roots the arm mentions, and admits no
path without `TargetRow.reachedAnchor()`. Two findings, one of them a
soundness hole:**

- **F1 (soundness, act before the round): a declared relative root domain is
  resolved against the SEED session's recorded value and asserted globally**,
  with the `varied()` check reachable only on the *undeclared* branch.
- **F2 (reporting): `MARKER_FLIPPED` and `CLOCK_SKEW` are returned without
  their polarity condition** — `polarityDecides` is computed and carried but
  never gates. Acceptance is still withheld (the alarm is BLOCKING), so this
  is a claim-kind-labelling issue, not an accepted-witness hole.
- **F3 (rule 5): an attach with no paired producer is dropped silently** from
  family closure, with no gap.

---

## 1. Design drift

### 1.1 Re-derivation — clean, and deliberately so

**Polarity**: `Composer:449-455` takes `target.phiTerm()` as published and
says so in the comment (*"the composer never re-derives the polarity"*). No
negation anywhere on the φ path. ✅

**Pairing**: `AttachRow.interaction()` (`AttachRow:111-114`) builds the
`Interaction` from the row's own `producer` endpoint; the composer never
searches for a producer by port, occurrence or family. ✅

**Endpoints**: `Endpoint`/`Interaction` are contract types with `id()`; the
composer consumes them and mints none. ✅

**Versions**: `stateJoins` (`Composer:598-629`) uses `read.observedVersion()`
and refuses when no write of that version exists in that session — *"There is
no 'latest write' and no choice between writers"*. ✅

### 1.2 Global assertions about per-session facts

Seven `assertNamed` sites. Four are per-path (`(=> selector …)`) and three are
global:

| assertion | global | verdict |
|---|---|---|
| `target_path_partition` (exactly-one) | yes | correct — it is the partition |
| `fatal_target` (or of selectors) | yes | correct |
| `path_fatal__<p>` | **no**, selector-guarded | correct |
| `handoff_family__<p>__<I>` | **no**, selector-guarded | correct (M4 deviation 1, and it is the right one) |
| `clock_floor__<cell>` | yes, `(>= cell 0)` | sound globally; CONTRACT-SPEC says "per path", the code says global `>= 0`. Harmless — a millisecond count is non-negative in every session — but it is a wording divergence worth recording |
| **`root_domain__<n>`** | **yes** | **F1, below** |

Arrivals and valuations are per path (`reads_p`, `valuation_p` inside the path
conjunction). ✅

#### F1 — the declared root domain is a per-session fact asserted globally

`Composer.domains():820-864`:

```java
RootMintRow row = seedRow(entry.getValue());     // the SEED session's row
RootDomain domain = domainOf(row);               // resolve(+k, row.recordedValue())
...
if (min != null && max != null && …) {
    lowering.assertNamed("root_domain__" + ordinal++,
            "(and (>= " + row.symbol() + " " + min + ") (<= " + row.symbol() + " " + max + "))");
    continue;                                    // <- returns BEFORE varied()
}
if (corpus.varied(row.rootId())) { … DIAGNOSTIC, no pin … }
```

`domainOf` (`:903-911`) resolves a relative bound against
`row.recordedValue()`, and `resolve` (`:921`) reads `+k`/`-k` as offsets from
it. So for a **declared** root the absolute window is computed from **one
session's** recorded value and asserted for **every** path. The `varied()`
guard — which exists precisely for this and is correct where it is used —
is unreachable on that branch.

Concrete case: `HDFS.BLOCK_KEY.SERIAL_NO`, declared `[+0..+3]` (REFACTOR-D3
§0). 11741 minted it fresh **13 times** and bug3 **12 times** across sessions;
the NN's serial advances, so sessions record different values. If the seed
recorded 119994, every path is pinned to `[119994, 119997]` and a session that
recorded 119997 has its own legal window `[119997, 120000]` excluded — its
disjunct closes for a reason nothing states. **This can turn a satisfiable
witness unsat, silently, on exactly the four key cases.**

Smallest fix, in the composer: move the `varied()` test above the declared
branch, and when a declared root's recorded value varies, assert the domain
**per path** against that path's own session's `RootMintRow` (the machinery is
already there — `reads_p` is per path). Failing that, raise
`UNSTATED_VALUE` BLOCKING rather than pin.

### 1.3 Arm selection keyed by the interaction — clean

`closeFamilies:647-736`: the queue is seeded from `attach.interaction()`, and
arms come from `corpus.attachesOf(interaction)` ∧
`corpus.exportsOf(interaction.producer())` matched on `producerSession`. Both
endpoints, and the producing run's own pairing. No port-only lookup, no
family string anywhere in `d3` (`grep` for request-family spellings: zero hits
in `d3/`). Nested v_H are closed transitively. ✅ R-I2.

### 1.4 Guard over roots the arm does not mention — clean

`guard(producerSession, text, guardRoots)` collects only roots that
`SmtLowering.mentions(text, symbol)` — a real token match with
`symbolCharacter` boundaries (`SmtLowering:217-235`), not `contains`. ✅
R-GUARD.

The arm's π prefix is `decision.seq() < export.seq()` (`Composer:739-756`) —
the producer's decisions up to the export. Sound, **and it is the one place
where cross-kind `seq` comparability becomes a hard runtime requirement**
(§2.1).

### 1.5 Paths admitted without `reachedAnchor` — none

`Composer:387-392` skips any target row with `!reachedAnchor()` and raises an
`ADMISSION_GAP`. A session with no path record at the occurrence is likewise
skipped with a gap. ✅

### 1.6 Claim kinds reachable without their polarity condition — F2

`ClaimPolicy.decide:148-211`:

```java
boolean polarityDecides = recorded != null && recorded.answer().unsat();
// 1. MARKER_FLIPPED  -> returned on the first sat non-zero valuation
// 2. CLOCK_SKEW      -> returned on a sat valuation with no root moved
// 3. RECORDED_FAILURE_EXPLAINED -> gated on flipsRefuted(outcomes)
// 4. MESSAGE_PAIRING_FLIPPED    -> gated on seedDisjunctUnsat(...)
```

Kinds 3 and 4 gate on their polarity condition. **Kinds 1 and 2 do not** —
`polarityDecides` is passed into `Claim.of(...)` as a field and never tested.
REFACTOR-D3 §1 states polarity as a condition on claims, not as an attribute.

**It is not an acceptance hole**: when the recorded valuation is sat on a
healthy-observed disjunct, `FORMULA_SAT_AT_RECORDED_VALUATION` is raised
**BLOCKING** (`:139-146`), which is exactly what withheld bug3 and 17897 in
round 1. So the effect is that the artifact says `MARKER_FLIPPED` + a blocking
alarm where the design says "no supported witness yet". Recommend: either gate
1 and 2 on `polarityDecides`, or state in the manifest that a claim kind is
only a finding when `polarityDecides && gaps has no BLOCKING`.

### 1.7 F3 — the silent drop

`closeFamilies:651-655`: `Interaction interaction = attach.interaction(); if
(interaction == null) continue;` — and `interaction()` returns null exactly
when `producer == null`. An unpaired attach therefore contributes no family
**and no gap**. Under rule 5 that must be a named row; `UNPRODUCIBLE_ANSWER`
or a new `PAIRING_MISSING` would do. It matters because §2.5 says the runtime
will produce unpaired attaches on day one.

## 2. What the composer expects that the runtime does not obviously publish

Each item is a concrete M2 requirement, with the row and field.

### 2.1 `seq` must be one monotonic counter across kinds, per session
`DecisionRow.seq` and `ExportRow.seq` are compared directly
(`Composer:751`). `ReadRow`, `WriteRow`, `AttachRow`, `TargetRow` also carry
`seq`; `ActivationRow`, `RootMintRow`, `GapRow` do not.
**Requirement**: `seq` is the VM's session-global event counter (today
`GlobalSymbolicSession::_next_event_id`), the same clock for every kind, never
a per-kind ordinal. If M2 numbers decisions and exports from different
counters, arm prefixes are silently wrong. **Also add `seq` to `RootMintRow`**
— a mint's position relative to an export is the same kind of question.

### 2.2 `javaType` spellings
`JavaSmtSorts.sortOfJava` accepts JVM descriptors (`Z B C S I J F D`,
`Lpkg/Cls;`), primitive names, box class names and `String`; **anything else
falls through to `Sort.REF`**, which for a numeric value is a wrong sort, not
a refusal. `ReadRow.javaType` feeds it directly (`Composer:617`).
**Requirement**: M2 publishes the JVM descriptor spelling (`I`, `J`, `Z`,
`Ljava/lang/String;`) on `ReadRow.javaType` and `AttachRow`; do not publish
`int`/`long` source spellings (they happen to work) and never a class name for
a primitive.

### 2.3 `LocationId.owner` for heap objects
CONTRACT-SPEC: `owner` = `<allocating Endpoint id>#<m>`. The legacy bridge
(`SmtLowering.locationKey(JsonObject):985-998`) still reads `ownerSymRid`.
**Requirement**: `WriteRow`/`ReadRow` carry `LocationId` with an
allocation-derived owner for `BlockKey` and every heap object the anchor
reads. `symRid` cannot be used: it is session-scoped and recycled — measured
**25 of 138 rids map to two classes across a corpus, 0 within one result**
(REPORT-ROUND1 §5). Without this, joins align only within a session, which is
all the current composer needs but not what R-I4 promises.

### 2.4 `observedVersion` on container-element reads
`stateJoins` joins only when `read.observedVersion() >= 0`, else pins to
`concreteValue`, else refuses. The NN's `BlockKey#24` read is a
**`ContainerRelation` owner with no `observedVersion` — 0 of 88 on bug3 and 0
of 208 on 11741** (REPORT-NNCHAIN §2). **Requirement**: M2 publishes
`observedVersion` on reads whose owner is a container element, or those reads
pin to a constant and the expiry sweep is never joined. This is the single
highest-value row field for the four key cases.

### 2.5 Producer pairing on attaches
`AttachRow.producer` is nullable and nulls are dropped silently (F3).
**Requirement**: every `AttachRow` carries `producer`; where the export ran
with no live region the producer is **degraded, not null** — `(node, role,
window-local k)` with `occurrence.lineageLost = true`. Today's runtime writes
the literal `"UNPLANNED"` with no node or role: **11 of bug3's expiry attaches
and 52 of 11741's** (REPORT-ROUND1 §8.3, REPORT-NNCHAIN §6).

### 2.6 Degraded producer endpoints must still be attested-flagged
`CorpusIndex.attested(session, occurrence)` = "that session has a path record
with ≥ 1 decision at that occurrence". A degraded producer has no path, so
`attested` is false and the arm is correctly UNATTESTED. **Requirement**: M2
must not fabricate decisions for an unfocused occurrence — the emptiness is
the signal.

### 2.7 The seed session is `ActivationRow.focused == false`
`CorpusIndex.seedSessionId()` returns the first session that *explored*
nothing. **Requirement**: the seed replay publishes `ActivationRow.focused =
false` for every activation, and **every focused replay sets it true on at
least one** — otherwise two sessions look like seeds and
`RECORDED_FAILURE_EXPLAINED` / `MESSAGE_PAIRING_FLIPPED` pick the wrong one.
Worth an explicit BLOCKING gap in the composer when more than one session
qualifies.

### 2.8 One name per root
M4 deviation 4 makes two `rootId`s sharing a symbol a BLOCKING gap and calls
it the runtime's obligation. **Requirement**: `RootMintRow.symbol` is unique
per `rootId` across the whole corpus, including across sessions and epochs.

## 3. The six-case oracle: which findings are reachable

Attestation rule: an arm is attested iff the **producer occurrence has a path
with decisions in that session** — i.e. iff it was a focused region somewhere
in the corpus. A witness may not move a root inside an unattested arm.

| case | interactions the composer needs families for | producers focusable? | reachable finding kinds |
|---|---|---|---|
| **17960** | **none** (one node, no wire) | n/a | `MARKER_FLIPPED` — unaffected by all of this. Passed round 1 and should stay. |
| **11741** | NN→Balancer DEK id; NN→DN heartbeat (block-key id, expiry); Balancer→DN SASL keyId | **yes for the NN side**: the rotation runs inside the balancer's request, so `REGION.08ab84c9`/`REGION.aaa1cfd7` are addressable and focusable today (REPORT-NNCHAIN §5). Round 1 already produced **6 attested expiry arms**. | `MARKER_FLIPPED`, `CLOCK_SKEW`, `MESSAGE_PAIRING_FLIPPED` — all three, and this is the case to calibrate on |
| **17897** | NN→client DEK id; NN→DN refresh-block-keys (id, expiry); DN→DN request DEK id | **no for the expiry producer until M2's daemon addressing**: the rotation is a daemon tick, occurrences are family-less (`region/REGION.…#k`), `HeartbeatManager$Monitor` 0% scoped | `MARKER_FLIPPED` only via **key-id** arms (attested, from focusable `refresh-block-keys` regions). **`CLOCK_SKEW` needs the expiry arm → UNATTESTED → root move refused** unless M2 lands daemon roots |
| **bug1** | NN→Balancer; NN→DN heartbeat; Balancer→DN (first hop) | expiry producer: daemon tick, same as 17897. **Second hop DN→DN carries no header at all** until the SASL scope-lifetime fix (REPORT-B1D) | `MARKER_FLIPPED` via key-id; the dn0 anchor is unaddressable until scope lands |
| **bug2** | NN→SPS; NN→DN heartbeat; SPS→DN | same daemon-tick shape as bug3/17897 | `MARKER_FLIPPED` via key-id; `CLOCK_SKEW` blocked on the same arm |
| **bug3** | NN→source-dn; NN→target-dn heartbeat; source-dn→target-dn | **no**: all 9 expiry phases' producers are `heartbeat#1` occurrences or `UNPLANNED`; 0 families in round 1 | `MARKER_FLIPPED` via key-id (serial). **`CLOCK_SKEW` refused by R-I5** — which matches the owner's note that bug3's finding is via serial |

**The line this draws for the round**: `MARKER_FLIPPED` through **key-id**
arms is reachable on all five HDFS cases today. `CLOCK_SKEW`, which needs the
**expiry** arm, is reachable **only on 11741** until M2 gives the daemon tick
an address and a focused replay. That is a prediction worth writing down
before the round rather than discovering in the verdicts: **if 17897, bug1,
bug2 or bug3 come back `CLOCK_SKEW`, either M2 landed the daemon address or
something is attesting an arm it should not.**

## 4. Two smaller notes

- `clock_floor__` is asserted once per cell globally; CONTRACT-SPEC §5 says
  "per path". Equivalent here, and I would leave it, but the spec and the code
  should agree in words.
- `CorpusIndex.attested` returns false for a focused occurrence whose path
  legitimately has **zero** decisions (a straight-line region). That is
  conservative in the right direction — an arm from it is UNATTESTED and root
  moves inside it are refused — but it will read as a surprise in a report, so
  it is worth a comment at the predicate.
