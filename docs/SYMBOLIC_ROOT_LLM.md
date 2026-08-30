# LLM-assisted symbolic-root selection

The LLM is a semantic proposer, not a program-analysis authority. GraphChecker
first freezes the target-first workflow and writes
`symbolic_root_mechanism_cards.json`. An external LLM classifies those cards;
the scheduler then checks the proposal against the exact catalog digest and
maps only validated `SELECT_ROOT` decisions to existing symbolic input actions.
The proposal cannot change target/producer closure, loop bounds, occurrences,
read-from, VM propagation, or Composer acceptance.

Cards are mechanism-level, not event-level. `relationBound=true` means the
card already has a scheduler-resolved writer and therefore cannot be selected
as a new root. Its `writerAnchors` name static producer sites; reader polling,
RPC/accessor copies, concrete event IDs, and bounded versions remain evidence
in the frozen plan instead of creating more candidate IDs. `symbolizable=true`
means only that `SELECT_ROOT` is permitted for that independent origin.

## Context to provide

Provide these inputs, in this order:

1. The bug report and the exact target branch with its required outcome.
2. The complete `symbolic_root_mechanism_cards.json`. Do not send the raw trace
   or raw static edge catalog.
3. For each still-`symbolizable` card, the defining method and at most one
   caller/callee hop. Include field/class comments when they explain lifecycle,
   ownership, caching, refresh, invalidation, selection, or expiry.
4. Short runtime aggregates keyed by the card's existing `evidenceIds`, such as
   observed task/region count and whether a value crossed an RPC or read-from
   edge. Do not replace evidence IDs with prose names.
5. The fixed-root list. Fixed roots are existing instrumentation authority and
   are evidence about one known witness, not the complete bug ground truth.

For HDFS-11741, explicitly ask the model to consider competing lifecycle
mechanisms: DataEncryptionKey caching/reuse, block-key rotation and
installation, expiry/time configuration, map membership, and the selectors or
guards that choose a version. `keyId` and `expiryDate` are current fixed roots,
not privileged answers.

## Prompt

```text
You are classifying an already enumerated set of symbolic-root candidates for
a bounded causal replay. You may use application semantics, names, comments,
and the supplied code excerpts. You must not invent program facts.

Goal:
- Preserve plausible alternative causal mechanisms for the supplied target.
- Within one mechanism, select only independent state/input origins. Derived
  copies, RPC payload fields, cached copies, lookups, selectors, and guards are
  context unless they are themselves an independent mutable origin.
- Do not force one global minimal answer. If mechanisms are alternatives,
  return a separate complete proposal JSON for each mechanism hypothesis.

Classification rules:
- ROOT / SELECT_ROOT: an independently changeable origin whose value may affect
  the target in this mechanism. It must have symbolizable=true and
  relationBound=false.
- CARRIER, SELECTOR, or GUARD / RETAIN_CONTEXT: causally explanatory, but do not
  mint another independent symbol there. A relation-bound symbolic action is
  required to remain `RETAIN_CONTEXT`, so Composer still receives its producer
  equality; a local context with no writer is kept concrete.
- STUTTER_NOISE or IRRELEVANT / EXCLUDE_SYMBOLIZATION: polling/retry repetition
  or state unrelated to this mechanism.
- REVIEW / REVIEW: evidence is insufficient. Never guess an ID or silently
  omit a candidate. REVIEW is a non-executable draft marker: GraphChecker
  rejects the proposal until a human resolves every REVIEW decision and
  resubmits it as one of the three executable decisions above.

Loop rule:
- Do not choose K, an iteration number, or an occurrence. Repeated polling
  reads and bounded writer versions do not create new root candidate IDs. The
  frozen task plan keeps every bounded occurrence and read-from arm after the
  mechanism-level decision.

Output contract for each proposal:
- Output JSON only.
- Use exactly this top-level shape:
  {"schemaVersion":1,"kind":"LLM_SYMBOLIC_ROOT_PROPOSAL",
   "authority":"PROPOSAL_ONLY","inputDigest":"<catalog inputDigest>",
   "decisions":[...]}
- Each decision has exactly candidateId, siteRole, decision, evidenceIds, and
  rootGroupId. rootGroupId is either a non-empty string or JSON null.
- Emit exactly one decision for every candidateId in the catalog.
- Cite at least one evidenceId belonging to that candidate.
- Use a non-empty rootGroupId only for SELECT_ROOT decisions. Roots belonging
  to the same mechanism use the same rootGroupId.
- Do not classify fixedRoots; the scheduler preserves them separately.

Before returning, check:
1. No unknown, duplicate, or omitted candidateId.
2. No invented or cross-candidate evidenceId.
3. No concrete-only card is SELECT_ROOT.
4. Every selected root is an origin, not another copy in the propagation chain.
5. Uncertainty is REVIEW, not an unsupported semantic claim.
```

If the output contains `REVIEW`, stop for human review. Do not pass that draft
to `campaign`; the deterministic validator rejects all unresolved review items.

## Offline workflow

Use two different, initially absent output roots and one shared external cache.
The first phase stops before concolic replay and writes the catalog:

```bash
export CAUSYNTH_OUTPUT_DIR=/absent/path/hdfs11741-catalog
export CAUSYNTH_CACHE_DIR=/persistent/path/graphchecker-cache
unset CAUSYNTH_SYMBOLIC_ROOT_PROPOSAL
./run_engine.sh --config <workflow.properties> catalog
```

The catalog is
`/absent/path/hdfs11741-catalog/schedule/iteration-0000/symbolic_root_mechanism_cards.json`.
Invoke the LLM outside GraphChecker, resolve any `REVIEW` items, and save one
strict executable proposal JSON. Then run the actual campaign in another fresh
root while reusing the same cache:

```bash
export CAUSYNTH_OUTPUT_DIR=/absent/path/hdfs11741-selected
export CAUSYNTH_CACHE_DIR=/persistent/path/graphchecker-cache
export CAUSYNTH_SYMBOLIC_ROOT_PROPOSAL=/absolute/path/proposal.json
./run_engine.sh --config <workflow.properties> campaign
```

Do not reuse the first output root: campaign directories are immutable. Keep
the workflow file unchanged between phases and pass the proposal through the
environment. The expensive seed-analysis cache key intentionally excludes the
plan-only proposal property while all other workflow properties still affect
the key.
The proposal itself is still frozen in campaign provenance, and the schedule
index commits both the catalog and proposal digests. A reduced run that finds
no witness is only evidence about that proposal; it is not a global
unreachability result.
