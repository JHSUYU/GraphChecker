# LLM-assisted symbolic-root selection

GraphChecker enumerates symbolic-root candidates and writes
`symbolic_root_mechanism_cards.json`. An external LLM may classify those cards;
the scheduler accepts only a complete proposal bound to the exact catalog
digest. The proposal cannot change topology, loop bounds, occurrences,
read-from choices, message propagation, replay, or Composer acceptance.

`relationBound=true` identifies context already tied to a selected writer. It
cannot become another independent root. `symbolizable=true` only means that a
`SELECT_ROOT` decision is permitted.

Candidate IDs, evidence IDs, and the catalog digest cover only stable program
and wire semantics. Runtime edge UUIDs, event numbers, goal IDs, and bounded
occurrences remain visible as evidence but cannot invalidate a proposal on the
next replay.

## Inputs

Provide:

1. The bug report and exact target outcome.
2. The complete mechanism-card catalog, not raw traces.
3. Small defining-method excerpts for still-symbolizable candidates.
4. Runtime aggregates keyed by existing `evidenceIds`.
5. Any fixed-root declarations already supplied to instrumentation.

The model may use application semantics but must not invent program facts.
Copies carried through messages, cached values, lookups, selectors, guards,
and state already tied to a selected writer remain context unless they are
independently mutable origins.

## Decisions

- `SELECT_ROOT`: an independently changeable origin with
  `symbolizable=true` and `relationBound=false`.
- `RETAIN_CONTEXT`: a carrier, selector, guard, or writer-bound value needed by
  the causal chain without minting a new symbol.
- `EXCLUDE_SYMBOLIZATION`: irrelevant state or bounded retry/polling noise.
- `REVIEW`: insufficient evidence. This is a draft marker; the validator
  rejects it until a human selects one of the executable decisions above.

Return one complete proposal per alternative mechanism. Do not choose loop
bounds, iterations, occurrences, or concrete event identifiers.

Use `CARRIER` for a value transported across a declared wire or local copy,
and `DERIVED_STATE` for a field/container value whose writer is already in the
selected causal closure. Both require `RETAIN_CONTEXT`; neither may become an
independent root. `ROOT` is reserved for an independently controllable origin,
such as time, configuration, input, or an external result.

## Output

Return JSON only:

```json
{"schemaVersion":1,"kind":"LLM_SYMBOLIC_ROOT_PROPOSAL","authority":"PROPOSAL_ONLY","inputDigest":"<catalog inputDigest>","decisions":[]}
```

Each decision contains exactly `candidateId`, `siteRole`, `decision`,
`evidenceIds`, and `rootGroupId`.

- Emit exactly one decision for every catalog candidate.
- Cite at least one evidence ID owned by that candidate.
- Use a non-empty `rootGroupId` only for selected roots in the same mechanism.
- Do not classify fixed roots.
- Do not submit a proposal containing `REVIEW`.

## Offline workflow

Use two fresh output roots and one shared cache:

```bash
export CAUSYNTH_OUTPUT_DIR=/absent/path/catalog-run
export CAUSYNTH_CACHE_DIR=/persistent/path/graphchecker-cache
unset CAUSYNTH_SYMBOLIC_ROOT_PROPOSAL
./run_engine.sh --config /absolute/path/workflow.properties catalog

export CAUSYNTH_OUTPUT_DIR=/absent/path/selected-run
export CAUSYNTH_SYMBOLIC_ROOT_PROPOSAL=/absolute/path/proposal.json
./run_engine.sh --config /absolute/path/workflow.properties campaign
```

Do not reuse the catalog output root. The proposal is excluded from the seed
cache key so the same frozen discovery can be reused, but its digest remains in
campaign provenance and the schedule index. Failure to find a witness after
narrowing is evidence only about that proposal.
