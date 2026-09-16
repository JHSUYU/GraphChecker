# REPORT-REVIEW-M3 — audit of d3/explore at staging `b8947723f`

Read-only. Against CONTRACT-SPEC, INTERACTION-ID, DESIGN3-PLAN, IDENTITY-V3,
REPORT-M3 §1–8. `d3/explore` = 2,831 lines / 12 files.

**Summary: the module is in better shape than the composer on the two rules
they share. Nothing re-derives polarity, pairing or endpoints; identity is by
id throughout and `lineage()` is never read, so it is V3-ready by
construction. Five findings, one of which is the mirror image of a composer
bug and shows which module is right.**

- **F1 (cross-module, act on compose not explore): explore resolves a declared
  relative root domain against the row of the session that reaches it, not a
  fixed seed session.** This is the correct rule, and it is the exact opposite
  of REPORT-REVIEW-M4 F1. Explore is right; compose should be changed to match.
  *But* explore picks the session by **drain order**, which works by accident
  of queueing rather than by construction (§2.1).
- **F2: the closure is over every attach/read of an occurrence, not only those
  its admitted paths read** — an over-approximation that is safe alone but
  meets a 64-task truncation that drops real members with a DIAGNOSTIC (§1.2).
- **F3: the arm guard is computed by a different rule in explore and in
  compose** — explore guards varied roots mentioned by the delivered
  expression *and the prefix*; compose guards every root mentioned by the
  expression only (§2.3).
- **F4: `Task.seedSessionId` means "first session containing the occurrence"
  in explore and "the session that focused nothing" in compose** — two
  notions, one field name (§1.4).
- **F5: explore names unpaired attaches and refuses them; compose drops them
  silently.** Explore's behaviour is the correct one (§2.4).

---

## 1. Closure (`ClosurePlanner`, 222 lines)

### 1.1 What it includes — the four terms are all there

`plan()` is a worklist over `OccurrenceAddress.id()`, seeded with the anchor:

- **anchor** ✅ — `pending.add(anchor)`.
- **transitive producers of the interactions its paths read, through nested
  v_H** ✅ — `producers()` (`:154-182`) adds `attach.producer().occurrence()`,
  then lowers every `ExportRow` at that producer endpoint and, for each
  symbol the lowering declares, looks up the corresponding attach **in the
  exporting session** and recurses. This is the NN → balancer → DN chain
  ending at the mint, and the recursion is cycle-guarded by attach endpoint id.
- **writers of read versions** ✅ — `corpus.writeOf(session, location,
  observedVersion)` → `writer.endpoint().occurrence()`.
- **state-connected co-occurrences on the anchor's node** ✅ — `stateConnected`
  collects the occurrence's read/written `LocationId`s and asks
  `corpus.touching(occurrence, location)`, whose index key is
  **`occurrence.node().render() + "|" + location`** (`Corpus:176, 306`). The
  node restriction is real, not just documentation.

A wire producer is made its own `Task`, never a `factor` — matching
DESIGN3-PLAN §3 ("a producer with no π … its own frontier").

### 1.2 F2 — the closure is not restricted to what the paths read

`successors()` iterates **`corpus.attachesOn(member)`** and
**`corpus.readsOn(member)`** — every attach and read that occurrence made in
any session — not the subset the admitted paths of the focused occurrence
actually read. The brief's rule is "interactions its paths read".

Alone this is a safe over-approximation. It stops being safe at
`DEFAULT_MAX_TASKS = 64`: the queue is FIFO, so spurious members enqueued
early can push genuine producers past the cut, and truncation is reported as
a single `ADMISSION_GAP` **DIAGNOSTIC** (`:85-90`). A closure missing a real
producer is not diagnostic — it silently removes an arm.

Two ways out, both cheap: filter `attachesOn`/`readsOn` to the symbols the
focused occurrence's decisions actually name (the machinery exists —
`FlipQuery`'s symbol fixed point does exactly this), or make truncation
**BLOCKING**. I would do both.

### 1.3 Keying — clean

`visited` on `occurrence.id()`; `taskId(focused) = sha16("task|" +
focused.id())`; `Task` recovered from the corpus by matching that id
(`taskOf`). **No request family anywhere in `d3/explore`** (grep: zero hits),
and **no occurrence ordinal is used as a key** — only ids. ✅

### 1.4 F4 — two meanings of "seed session"

`ClosurePlanner.seedSession()` (`:212-221`) returns the **first session in
corpus order** that has an activation or decisions at the occurrence.
`Composer`/`CorpusIndex.seedSessionId()` returns **the session that focused
nothing** (`ActivationRow.focused == false`). Both populate fields named
"seed session". They will differ as soon as a focused replay of the anchor is
read before the seed, and `Task.seedSessionId` is what a worker replays from.
Recommend: one helper, the `focused == false` definition, used by both.

## 2. Obligations (`ObligationFactory` 276, `FlipQuery` 611)

### 2.1 Roots and domains — right rule, fragile mechanism

`FlipQuery.root()` (`:238-262`): a MARKER that is `declared()` is left free
(both values); a root with no domain is **pinned to `row.recordedValue()`**
with a stated reason; a root with a domain gets
`(and (>= v min) (<= v max))`; a CLOCK gets `(>= v 0)` and nothing else.
`Corpus.domainOf` (`:371-382`) resolves `+k`/`-k` against
**`root.recordedValue()` of the row it was handed**, and that row is
`corpus.root(ref.sessionId, ref.symbol)` — **the session whose symbol pulled
it in**. ✅ the brief's requirement, and the correct rule.

**The fragility**: the variable is keyed `root|<rootId>` — one name across
sessions — and `if (!explained.add(variable)) return;` means **the first
session to reach it fixes the window for the query**. In practice the
obligation's own decisions are renamed first and `enqueue` appends to a FIFO
`ArrayDeque`, so the obligation's session drains first and wins. That is
correct today **by queue order, not by construction**. One line — prefer the
row whose `sessionId` equals the obligation's path session — makes it a
property instead of a coincidence, and it is worth doing because the same
mistake in compose (F1 there) is a live soundness bug on `SERIAL_NO`.

### 2.2 Prefix and flip

`ObligationFactory` builds, per admitted path and per decision whose predicate
mentions a root, a `v_H` or a clock, the prefix decisions **in the arms they
took** ∧ **the complement** of the flipped decision. ✅ "prefix as recorded
∧ ¬d". A query the solver refuses or answers UNSAT is closed without issuing a
replay.

### 2.3 F3 — the family and its guard, and where it diverges from compose

`handoff()` (`:265-306`): arms come from `corpus.exportsAt(attach.producer())`
— keyed by **both endpoints** (the attach's own `producer` and its own
`endpoint`), never by port alone. ✅ R-I2. Nested `v_H` are closed to a fixed
point by the `pending`/`explained` worklist with a 100,000-step guard. ✅

`arm()` (`:353-421`):
- prefix = the producer's decisions with **`decision.seq() < export.seq()`** ✅
  identical to compose;
- `(= v_H e_q)` ✅;
- `attested = corpus.ranFocused(exportSession, producerOccurrence)`, i.e.
  `ActivationRow.focused` — and an unlowerable export falls back to
  `recordedValue` with `attested = false`. An unattested arm raises
  `UNATTESTED_ARM` DIAGNOSTIC. ✅ R-I5.

**The divergence**: the guard is
`for (String rootId : roots) if (corpus.varied(rootId)) …`, where `roots` is
accumulated by `rename()` over **the delivered expression *and* the prefix
terms**. Compose's `guard(producerSession, text, guardRoots)` takes **only the
delivered text**, and applies **no `varied` filter**.

So on one arm the two modules can pin different root sets: explore pins
prefix-mentioned varied roots that compose does not, and compose pins
expression-mentioned invariant roots that explore does not. Neither is
obviously wrong — but R-GUARD is one rule and there are two implementations of
it, in the module that proposes a flip and the module that judges it. **A flip
explore proves satisfiable can be refused by compose, and the difference will
read as a solver disagreement.** Recommend a single shared `Arms` helper, the
way `SmtLowering` is already shared.

### 2.4 F5 — no-arm handling, and the unpaired attach

- A **control** (attach on the focused occurrence) with no arm: variable left
  **free**, `registerControl(..., unproducible = true)`, `UNPRODUCIBLE_ANSWER`
  DIAGNOSTIC. ✅ exactly the brief.
- A **nested** handoff with no arm: pinned to `attach.arrival()`; if there is
  no arrival either, `UNPRODUCIBLE_ANSWER` and the symbol stays unexplained. ✅
- An **unpaired** attach (`producer == null`) gets the variable key
  `unpaired|<consumer endpoint id>`, a refusal reason, and — when it is a
  control — `unproducible` + a named gap.

**That last point is the contrast worth acting on**: compose's
`closeFamilies` does `if (interaction == null) continue;` with no gap
(REPORT-REVIEW-M4 F3). Explore names it. Same input, one module speaks and one
is silent; explore has it right.

### 2.5 Clocks and state reads

Clocks: keyed `clock|<rootId>|<sessionId>` — **per path by construction**,
unbounded, `>= 0` only. ✅ Exactly DESIGN3/CONTRACT-SPEC.

State reads (`read()`, `:308-340`): join the write of the **observed
version in the same session**, else the stated `concreteValue`, else refuse
naming it. ✅ No "latest write", no cross-session version guessing.

## 3. Admission per task — clean

`Frontier` (148 lines) documents and implements it: *"Admission is per task.
`NOT_ADMITTED` says the focused occurrence's own prefix was not reproduced"*.
`NOT_ADMITTED`/`DIVERGED` close their own query and are never retried with the
same id; a `VALIDATED` replay's session enters the corpus and yields new
obligations next wave. **No verdict of one task closes or gates another**, and
there is no producer-prefix coupling anywhere in `ObligationFactory` — which
is precisely the linked-replay defect being deleted (11741 round 1: 26
`REPLAY_NOT_ADMITTED`). ✅

## 4. Waves — clean, with the loop owned outside

`ExploreMain` is **one invocation = one wave**: it reads the sessions and the
prior `ObligationResult`s, rebuilds the frontier from recorded verdicts, and
writes the flips no wave has answered. *"It never solves"* — solving and
replaying are the campaign's workers, which is what makes the workers parallel
and the wave a union of per-task frontiers. Fixed point per task lives in
`Frontier`; the wave index is carried in the manifest. ✅ DESIGN3 §3/§6.

One consequence worth stating: because the process never solves, **`--max-tasks`
truncation and any closure omission are invisible to the campaign except as a
gap row** — reinforcing F2's "make truncation BLOCKING".

## 5. Re-derivation and global assertions — clean

- **Polarity**: `d3/explore` never reads `phiTerm`, `observedFatal` or
  `reachedAnchor`. A flip query is built from decisions and their complement;
  the fatal arm is compose's business. ✅
- **Pairing**: the single `Interaction.of(...)` call (`FlipQuery:478`) is a
  *key construction* from the row's own `producer` and `endpoint`, not a
  search. No arm is found by port, occurrence or family. ✅
- **Endpoints**: never minted; read from rows. ✅
- **Global assertions**: a flip query is one path by construction, so the
  question reduces to cross-session collapse. Handoffs collapse to one
  variable per **interaction** (correct under INTERACTION-ID), clocks are per
  session (correct), roots are one variable corpus-wide (correct — a root is
  one quantity), reads are per session+endpoint (correct). ✅

## 6. What explore needs from M2, beyond REPORT-REVIEW-M4 §2

Everything in that list still applies. Four additional, explore-specific:

1. **`ActivationRow.focused` must be published for every activation of every
   session**, not only focused ones. `Corpus.ranFocused` returns false when
   the activation row is *missing*, which is indistinguishable from
   `focused=false` — so a dropped activation row silently turns an attested
   arm into an unattested one and refuses a witness. Row: `ActivationRow`,
   field: `focused`, requirement: one row per activation per session.
2. **`ExportRow.seq` and `DecisionRow.seq` must be comparable for the
   *producer's* occurrence** (`arm()` compares them directly). Same
   requirement as REVIEW-M4 §2.1 but it bites here first, because explore
   computes arms before compose ever runs.
3. **`AttachRow.arrival` must be stated for every nested handoff**, including
   ones the session did not answer: it is the pin of last resort
   (`handoff()`), and without it the symbol is left unexplained and the
   obligation is refused.
4. **`RootMintRow.declared`** distinguishes a marker that is free in
   `{recorded, flipped}` from one that must be pinned (`root()`:
   `if (row.kind() == MARKER && row.declared()) return;`). M2 must set it from
   the case declaration, not from whether a domain happens to be present.

## 7. IDENTITY-V3 readiness

**The contract is still V2** at this head: `OccurrenceAddress` carries
`List<LineageHop> lineage` and `Endpoint` carries `int ordinal`. V3 replaces
both with `CausalContext` + `ExecutionIndex` and a site-local `siteIndex`.

**Explore is ready, and for the right reason: it never reads address
internals.** Grep over `d3/explore` for `.lineage()` → **zero hits**. The only
address accessors used are `id()`, `node()` (for the state-connection key, and
V3 keeps `NodeId`), `equals()` and `render()` — and `render()` only in
gap/manifest text.

Three places that touch an ordinal, and what each needs:

| site | use | under V3 |
|---|---|---|
| `FlipQuery:484` `"vH_" + site + "_" + endpoint.ordinal()` | a readable SMT variable **name** | must render `siteIndex` (or the endpoint id's prefix); the **key** beside it is already `handoff\|<interaction.id()>`, so only cosmetics break |
| `FlipQuery:497` `"st_" + slot + "_" + endpoint.ordinal()` | same, for a state read; key is `read\|<session>\|<endpoint.id()>` | same |
| `ObligationFactory:93/135/192/247/266/271`, `FlipQuery:185/193/591`, `ExploreCodec:63`, `ObligationSolverMain:161` — `decision.ordinal()` (11 of the 13 `ordinal()` calls in the package) | `DecisionRow.ordinal`, the k-th execution of a decision **site** | **unaffected** — IDENTITY-V3 §4 leaves rows unchanged and this is not an endpoint ordinal |

So the V3 migration should touch `d3/explore` in **two name-building
expressions** and nothing else. That is worth stating loudly, because it is the
payoff of the id-only discipline and it should be preserved: if the migration
tempts anyone to expose `ExecutionIndex` to explore for "better names", the
coupling comes straight back.

One V3 item that does land here later: **`Corpus.touching`'s key is
`node().render() + "|" + location.toString()`**, and `LocationId.owner` is
today a session rid. Once §5's Memory Indexing gives owners an allocation
endpoint id, this key becomes cross-session valid and `stateConnected` starts
finding co-occurrences across sessions rather than within one. That is an
improvement, but it will widen every closure — worth re-measuring `--max-tasks`
against the six cases when it lands (see F2).
