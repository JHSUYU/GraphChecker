# REFACTOR-D3 — master plan: rebuild GraphChecker on Design 3 and run the six cases

Owner directive 2026-09-14: stop incremental fixes; refactor the existing code to the
priority design (region-local symbolic propagation + anchor/interaction-keyed symbolic
merging, focused-region replays, causal-graph partial-order merge, solve → materialize
→ validate) and get the six cases through. Spec documents (read in this order):
graphchecker-core-design-principle (memory), DESIGN3-PLAN.md, INTERACTION-ID.md,
IDENTITY-V2.md, this file. Constraints: ≤ 100 @Test (target ≤ 80), src/main net
smaller than today, no debugging instruments in src/main, no edits in /opt/hadoop-*
except declared workload diffs, never git checkout/stash/reset/clean there, one build
step per tool call, Java 8 hadoop builds only as documented in the runbook.

## 0. What the six cases must check (the oracle the refactor serves)

| case | fatal read (anchor) | interactions on the closure | roots that may move | expected finding kinds |
|---|---|---|---|---|
| 17960 | NN serializeSnapshotSection#u61 | none (one node) | config marker SNAPSHOT_DELETION_ORDERED | MARKER_FLIPPED (passes today) |
| 11741 | DN retrieveDataEncryptionKey: allKeys.get(keyId)==null | NN→Balancer (DEK id), NN→DN heartbeat (block-key id, expiry), Balancer→DN SASL (keyId) | SERIAL_NO [+0..+3], expiry (NN clock), DN clock (unbounded) | MARKER_FLIPPED (rotation), CLOCK_SKEW (expiry sweep), MESSAGE_PAIRING_FLIPPED |
| 17897 | same read on dn0 (striped checksum) | NN→client DEK id, NN→DN refresh-block-keys (id, expiry), DN→DN request (DEK id) | same | same |
| 17899 bug1 | same read on dn1 (balancer first hop) | NN→Balancer, NN→DN heartbeat, Balancer→DN | same | same |
| 17899 bug2 | same read on target-dn (SPS) | NN→SPS, NN→DN heartbeat, SPS→DN | same | same |
| 17899 bug3 | same read on target-dn (replicate-block from source-dn) | NN→source-dn, NN→target-dn heartbeat, source-dn→target-dn | same | same |

Target-region state: allKeys = put(v_H(id), key(v_H(expiry))) from heartbeat attaches,
removeIf(expiry < now) with the DN clock, get(v_H(request id)). The solver may change
only: put keys/values (through v_H), removeIf guards (clock/expiry), the request key
(through v_H); the operation sequence of an executed path is fixed — a different
sequence needs a different explored path (a flip in the writer region).

## 1. Architecture (target state)

Pipeline: PLAN → INSTRUMENT → REPLAY(seed) → IMPORT → EXPLORE(focused tasks, waves)
→ COMPOSE → SOLVE → DECIDE → EMIT, iterated per topology epoch. (Owner ruling: NO VALIDATE / materializing replay — the composed .smt + z3 verdict is the deliverable.)

Identity: OccurrenceAddress v2 = node#epoch / lineage (role#k / role@api#k / …) /
region#k (IDENTITY-V2). Endpoint = (occurrence, site/port, ordinal[, attempt]).
Interaction = (kind, producer endpoint, consumer endpoint) (INTERACTION-ID). Locations
replay-stable (static field; object = allocating occurrence + site + m).

Rows per replay session (all keyed by session + occurrence): Activation(lineage),
Decision(π terms with clock readings), Export(endpoint, e_p, handle), Attach(endpoint,
v_H, arrival, answered?, pairing to the producer endpoint), Write(endpoint, location,
version, expr), Read(endpoint, location, observed version), RootMint(root id, symbol,
recorded value, domain), Target(φ in the fatal polarity, observed arm), Gap/Telemetry.

Exploration: task = one focused occurrence (or one state-connected factor); everything
else concrete with exports recorded and attaches minting v_H (entry rule); obligation
= prefix ∧ flipped arm with handoff controls bound to interaction families (producible;
otherwise flagged unproducible); answered values applied at the attach; admission per
focused region; fixed point per region; waves = union of frontiers; parallel workers.

Composition per anchor (factorized): for each admitted consumer path p:
selector_p ⇒ π_p ∧ φ_fatal ∧ reads_p, reads_p = ⋀ over interactions I read by p:
v_H(I) = answered_p(I) | e_paired(I) (attested arm, root-carrying) | x_p(I) (own
arrival, per path); families: for each I on selected paths ⋁_q (π_q ∧ guard_q(roots
e_q depends on) ∧ v_H(I) = e_q), attested flag per arm; state joins read := write
version expression by (writer endpoint, version); identities ≠ null, distinct per
session; clocks per path, unbounded; root domains relative; declared roots enumerated.
Claims: MARKER_FLIPPED, CLOCK_SKEW, MESSAGE_PAIRING_FLIPPED, RECORDED_FAILURE_EXPLAINED;
polarity (recorded valuation unsat for the seed disjunct); a witness may not move a
root inside an unattested arm. No VALIDATE stage (owner ruling): the claim from DECIDE is
the verdict.

## 2. Milestones, owners, gates

D DELETION FIRST (owner directive 2026-09-14: old code deleted outright, NO compatibility
layer, no adapters, no stubs) — one agent, one commit per mechanism, tree compiles and the
suite runs after each: linked replay/companions/slices, request-family addressing,
phase-keyed handoff families + VmHandoffEvidence shape + NO_ACTIVE_REGION/MISSING_METADATA
plumbing, composer global pins/per-port naming/family filter/coverage-closure machinery,
election ranking, importer folds of the single-row shape, and their tests. Keep the 21
workload-called APIs and the four live-reader mechanisms named in the runtime inventory.
Report REPORT-D.md with line counts. Then M1.

M1 CONTRACT (1 agent, ~1 day) — package contract/: Endpoint, Interaction,
OccurrenceAddress v2 (+ v1 parse for existing case declarations), the row records
above, Family, CompositionManifest, ClaimKinds; JSON codec; delete superseded
contracts (HandoffPhaseContract as key, VmHandoffEvidence shape, request-family
address parts). Gate: contract tests (folded), schema doc, staging builds with the old
consumers adapted only where compilation requires.

M2 RUNTIME (1 agent, ~2 days, after M1) — lineage scope (parent+role; Server.Call
carry; SASL inbound scope = DataXceiver op; daemon roots), OccurrenceMinter v2, rows
with both endpoints (port ordinal, attempt, pairing), mint at every declared port,
focused-region replay mode. Delete companions/slices, NO_ACTIVE_REGION paths, request-family addressing.
Gate: six recordings re-taken on the new runtime; per case: lineage-complete share
per entry point, every declared port mints, interaction rows paired.

M3 EXPLORE (1 agent, ~1.5 days, after M1, parallel with M2 against the contract) —
focused tasks, obligations with interaction families (from HandoffFamilyRows generalised
to interactions), per-region admission, waves. Delete ConcolicPathFlipPlanner
companions and linked-slice admission. Gate: on 17897/bug3 recordings the target
region reaches the fatal arm with producible answers; NN rotation explored as its own
task.

M4 COMPOSE (1 agent, ~2 days, after M1, parallel) — the factorized composition above,
families by interaction, arm guards limited to relevant roots, per-path reads, state
joins by endpoint, identities, clocks, domains, enumeration, ClaimPolicy kinds, declared election only. Delete global pins, per-port naming, request-family arm
filter, ranking election, gap kinds without a consumer. Gate: invariants in one
composer test (healthy path unsat at ordinal 0; fatal path sat; arms by interaction;
unattested arm blocks root moves) + offline on M2/M3 corpora.

M5 CAMPAIGN (runtime agent, ~1 day, after M2–M4) — run_engine stages,
epoch loop on interaction divergence, delete slice/coverage machinery superseded;
shell helper tests. Gate: one jar, six cases, two lanes.

M6 SIX-CASE ROUND + landing — verdict per case with finding kind (the composed .smt + z3);
staging → main; final report with line counts (before/after) and test count.

Integration: I merge each milestone branch into staging with the guarded procedure;
staging must build and pass at every merge; M2/M3/M4 rebase onto M1 daily. Test cap
enforced at every merge (count ≤ 80 target). Reports per milestone under d-refactor/.

## 3. Time
M1 day 1; M2–M4 days 2–4 (parallel); M5 day 5; M6 days 5–6. Risks: scope loss in
Hadoop thread pools (M2 measures per entry point; a case whose anchor cannot be
addressed degrades to node-level with a named gap); recordings must be re-taken on
the new runtime (all six); z3 cost on bug1 (large trace).
