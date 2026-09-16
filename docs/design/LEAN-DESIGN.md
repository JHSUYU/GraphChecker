# LEAN DESIGN — GraphChecker, the whole thing on one page (2026-09-15, owner-directed simplification)

Owner's frame: the design is the fixed core principle; everything not derivable from it is deleted. This page is the
reference the planner judges every component against. Anything in the tree that this page does not name is a deletion.

## 1. What is symbolic — and nothing else
A symbol is minted at exactly three kinds of places, all declared by the case:
1. **Roots** — fault markers, configured sources (serial/expiry via hooks), clock cells. `RootMintRow`.
2. **Declared region inputs** — a cell the case names in `symbolic-inputs.jsonl`; the read mints a placeholder symbol S
   for the value read. `ReadRow` with `symbol=S, observedVersion (last real write) | concreteValue, mintVersion`.
3. **Wire attaches** — an IN port receives a message leaf; the attach mints v_H and pairs it with the producer's export.
   `AttachRow`/`ExportRow`.
Everything else is concrete until a symbolic value is WRITTEN into it: the VM keeps shadows by value under the real object,
and a read then returns the expression (a container read carries the recorded base inside the expression). No region-entry
container/reference/"carrier" inputs, no receiver locators, no window-start deliveries, no tracked carriers. The static
slice decides only which regions are instrumented and which write sites of a declared cell are observed.

## 2. What a replay publishes (rows; one event = one row; one symbol spelling; every EXPR ref in the table)
- `ActivationRow(occurrence, focused, instrumented, threadKey, startedBy)` — identity v3 = (node#epoch, region,
  causal context, execution index).
- `DecisionRow(occurrence, site, ordinal, term = the jump's predicate (site-stable), outcome = taken)`.
- `RootMintRow`, `ReadRow`, `WriteRow(location, version, expr, writer occurrence)`, `ExportRow`, `AttachRow`,
  `TargetRow(φ in the fatal polarity, observedFatal, reachedAnchor)`, `GapRow`.
- Endpoint = (occurrence, site, siteIndex) — the VM states the site, the runtime the frames.
- **IMPORT gate**: the contract's invariants (never-neither, refs present, one row per event, one sort per symbol,
  outcome consistent with the recorded roots, every version stated by a writer or a mint, no fabricated write, roots
  declared only, φ polarity, the flip really flipped). BLOCKING fails the campaign by name.

## 3. Explore (collect the arms the seed lacks — never validation)
- Wave tasks = the anchor's row-driven closure ∪ every instrumented seed occurrence with a **symbolic decision**
  (any non-empty term).
- Obligation = prefix ∧ ¬d; the solver binds v_H through families; a model on a symbol nobody binds = UNPRODUCIBLE.
- One focused replay per obligation, in parallel (workers); the focused row confirms the flip by `outcome`;
  ADMITTED / NOT_ADMITTED / DIVERGED. Closure recomputed per wave; slots by (producer endpoint, consumer endpoint);
  replacement (new epoch) only for a WIRE pairing that contradicts another session's; STATE re-pairing is a path fact.

## 4. Compose (align + merge + lower + gate)
Fatal_T = ⋁_p ( selector_p ⇒ π_p ∧ φ_p ∧ reads_p ∧ valuation_p ), one path per anchor activation per session.
- reads_p: each read joins to the expression of the version it observed (WriteRow of the same session) or to its
  placeholder (mintVersion), else pins to the recorded value; identities opaque and distinct; wire reads by families.
- valuation_p: the session's recorded value of every VARIED root; arm guards carry the delivering replay's valuation.
- Roots by kind: MARKER free in {recorded, flipped}; INTEGRAL in its declared relative window; CLOCK ≥ 0; else pinned.
- One lowering (quantifier-free where the recording states the size); z3 per valuation; `unknown`/`error` = named gap.
- Claims: MARKER_FLIPPED, CLOCK_SKEW, MESSAGE_PAIRING_FLIPPED, STATE_PAIRING_FLIPPED, RECORDED_FAILURE_EXPLAINED,
  NO_SUPPORTED_WITNESS; polarity gate = the recorded valuation's disjunct is unsat.

## 5. Deleted (not derivable from §1–§4)
Carrier layer (region-entry container/reference inputs, `BOUNDED_CONTAINER_STATE`, `REFERENCE_CARRIER`,
`ACTIVATION_FIELD_RECEIVER` tracking, `carrierSlice`, `observeWithoutMinting`); WINDOW_START rows; task-plan roots;
clock windows; dual declaration tables/tokenizers/expression-ref spellings; branch-record cluster (S2);
`RuntimeRefinedGraphBuilder`; every compat layer, adapter, fallback, ignored option; the `d3` package naming (flatten
to contract/compose/explore/plan/smt) and the handover clutter in the repo root.

## 6. Cost model
Seed: one replay per case. Explore: Σ obligations per wave, run in parallel (workers), waves until the frontier closes.
Compose: seconds. A campaign per case for acceptance; everything else offline on kept corpora.
