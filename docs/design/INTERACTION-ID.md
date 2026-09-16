# INTERACTION-ID — one interaction, two endpoints

Owner's rule (2026-09-14): an interaction in the causal graph is identified by its
TWO endpoints, combining tracing (within-run pairing), lineage (cross-run naming of
each side), occurrence (which activation) and ordinals (which event of that
activation). Companion of IDENTITY-V2 and DESIGN3-PLAN.

## 1. Definitions

endpoint  = (node#epoch, occurrence, site, ordinal[, attempt])
  node#epoch   the component instance and its topology epoch
  occurrence   the activation's address (v1: family@source/api#k; v2: lineage + per-hop k)
  site         for a wire edge: the declared PORT (transport, direction, request/response
               half, field path); for a state edge: the WRITE or READ site (class, method,
               bytecode index, location kind)
  ordinal      the k-th event of that site inside that occurrence (loop bodies count inside
               their enclosing invocation, LOOPOWN)
  attempt      retry number when the transport retries (wire edges only)

interaction = (kind, producer endpoint, consumer endpoint)
  kind = WIRE (export → attach) or STATE (write version → read of that version)

Within ONE run the pairing is a recorded fact: WIRE by the exchange correlation id and
the expression handle (export → attach), STATE by the version (write vN → read observed
vN). Across runs an interaction is THE SAME iff both endpoints are equal component-wise.
Neither endpoint alone identifies it: the consumer side alone (today's handoff phase =
consumer occurrence + port + k) admits a different producer that happened to serve the
same k-th attach; the producer side alone admits a different consumer.

## 2. Rules

R-I1 (publication). Every handoff row and every state-edge row carries both endpoints in
full and the within-run pairing evidence (correlation/handle or version). A row whose
producer endpoint cannot be named (scope lost, daemon tick) carries a DEGRADED producer
endpoint (node, role, window-local k) with `lineageLost=true` — the interaction still
exists and is still keyed by both endpoints.

R-I2 (family key). A family is keyed by the interaction, not by the consumer phase:
  family(I) = ⋁_q ( π_q ∧ v_H(I) = e_q )  over producer paths q whose export endpoint
  equals I.producer AND whose run paired that export with I.consumer.
A producer path with the same port but another endpoint (heartbeat#2 vs #1, another
node, another attempt) contributes NOTHING to family(I). A consumer path p reads v_H(I)
only if p's run paired p's attach endpoint with I.producer.

R-I3 (divergence). If a replay pairs a consumer endpoint C with a producer endpoint P'
≠ the epoch catalog's P for C, that is a topology divergence (new interaction), not a
path variation: the run's rows go to the next epoch, never into family(P→C). A missing
interaction of the catalog on a selected path = admission gap. An extra interaction
outside the anchor's closure = recorded, ignored.

R-I4 (state edges, same form). writer endpoint = (occurrence, write site, k-th write)
producing version vN of location L; reader endpoint = (occurrence, read site, k-th read)
observing vN. The join in COMPOSE (read := write version's expression) is the STATE
family with exactly one arm per run; across runs the arm set is the writer paths whose
endpoint equals the writer endpoint. Locations are replay-stable per IDENTITY-V2 §4.

R-I5 (attested vs unattested arms). An arm from a producer path with a recorded π is
attested; an arm from a run in which the producer ran concretely (export recorded, no
π) is UNATTESTED — usable to state what was delivered, not to move a root: a witness
may not move a root that occurs in an unattested arm's e_q (fail-closed until the
producer is explored as a focused region).

## 3. What changes against today

| today | with INTERACTION-ID |
|---|---|
| handoffPhaseId = hash(consumer occurrence, port, k) | interactionId = hash(producer endpoint, consumer endpoint, kind); phaseId kept as the consumer half |
| rows carry producerOccurrenceId / exportEventId / attachEventId | rows carry the full producer endpoint incl. port ordinal + attempt, and the consumer endpoint; degraded producer endpoints named, not dropped |
| arms selected by phase, filtered by "producer in the anchor's request family" | arms selected by interaction (both endpoints); request family plays no role |
| unproduced arrival: no arm | unattested arm (concrete export) states the delivery; per-path pin is its degenerate form |
| divergence = unplanned occurrence/binding | divergence = an interaction (pair) not in the epoch catalog |
| state join keyed by (location, version) within a run | same, plus the writer/reader endpoints so cross-run alignment is by endpoint, not by version number |

## 4. Where it lands (with IDENTITY-V2 phases)

Phase 1 (rows): runtime publishes both endpoints + ordinal + attempt on every WIRE row
and both endpoints on every STATE row (VmHandoffEvidence, write-log rows); degraded
producer endpoints for scope-less exports (this is the entry rule's addressing half).
Phase 2 (keys): HandoffPhaseContract gains the interaction key; HandoffFamilyRows
selects by interaction (shared by composer and flip planner); R-I5 flag on arms;
ClaimPolicy refuses root moves inside unattested arms.
Phase 3 (epoch): the epoch catalog is the interaction set of the anchor's closure;
divergence = pair not in the catalog.
Tests fold into HandoffBelongsToItsConsumerTest / OccurrenceAddress tests (cap 61):
two producers, same port, same consumer k → two interactions, two families; a retry →
attempt distinguishes; a scope-less producer → degraded endpoint, unattested arm.

## 6. Slots (owner, 2026-09-15) — R-I6 replaces R-I3's divergence rule

A SLOT is an interaction identity (kind, producer endpoint id, consumer endpoint id) in
the epoch's skeleton; the skeleton is the slot table; family(slot) = every producer arm
whose run paired those two endpoints. Rows from any replay, any worker, any wave fall
into slots by the two endpoint ids alone.
- New interaction whose consumer is a closure member → OPEN a slot: the skeleton grows
  monotonically; this replay's arm is the slot's first; the next wave lists the slot's
  producer occurrence as a task (ClosurePlanner). No epoch.
- Same pair seen again by any later replay → falls into the slot; arms accumulate.
- Interaction outside the closure → recorded (DIAGNOSTIC), never a slot.
- REPLACEMENT — a consumer endpoint already in a slot pairs with a different producer
  endpoint, or a closure member's CausalContext changes → contradiction, not growth →
  TOPOLOGY_DIVERGENCE → new epoch (the old slot table is kept; the new one starts from
  the divergent replay's pairing).
Consequences: growth is the normal case; only replacement forks; parallel workers fill
slots independently and merging is per slot.

## 7. Shared fields in the same framework (owner, 2026-09-15) — R-I7 relaxes R-I4

A STATE slot = (writer endpoint, reader endpoint) on one location; a loop iteration's read
is its own reader endpoint (the execution index carries the iteration); within a run the
version pairs them. R-I7: family(STATE slot) may hold MORE THAN ONE writer arm — every
attested writer path of that location whose version is eligible for the reader under the
run's happens-before (versions the reader could have observed: the observed one and the
writes ordered before the read in that session, bounded by the location's version chain)
— so the solver chooses the interleaving instead of a replay per order; an unattested
writer arm states its delivery only (no root inside it may move). A reader paired with a
writer outside the eligible range is REPLACEMENT (R-I6 → epoch); a new reader/writer pair
inside the closure opens a slot. The VM supplies the rows (write log with version
expressions from the shared expression table; live observed version on reads).

### 7.1 R-I7 tightened (planner, after the tricky cases) — this supersedes the paragraph above
- ELIGIBLE ALTERNATIVES for a reader occurrence R on location L = writer OCCURRENCES W
  that are HB-CONCURRENT with R: not ordered before/after R by program order (same
  thread seq), message causality (the CausalContext/Anchor chain), or thread start/join.
  Locks are NOT constraints (they forbid overlap, not order). A writer ordered before R
  contributes its version as a fact; one ordered after contributes nothing.
- GRANULARITY = occurrence: W's writes to L move as a block, either wholly before or
  wholly after R's reads of L; all reads of L inside R take the same choice (no writer
  interposed between two reads of one occurrence — check-then-act stays atomic because
  we do not record locks and must not synthesize what a lock may forbid).
- ATTESTED ONLY: only writer occurrences with a recorded π are alternatives; unattested
  or Lost-context writers state their delivery only. HB unknown (Lost) ⇒ no alternative.
- Loop iterations: each read is its own reader endpoint; drift of the execution index
  from interleaving-dependent iteration counts is handled by two-level matching.
- Finding kind STATE_PAIRING_FLIPPED: the witness reaches the fatal arm with roots
  recorded but with L delivered by a different eligible attested writer occurrence than
  observed; polarity = the observed pairing's disjunct is unsat.

## 8. Outside the closure (owner, 2026-09-15) — three cases
After every wave the closure is recomputed from the anchor over ALL accumulated rows
(Pred_W fixed point). A flipped path that reaches something outside the previous closure:
1. Inside G_S^W (instrumented regions), not yet in the closure → it enters the closure by
   the fixed point; its interactions open slots (R-I6), the skeleton grows, its producers
   become tasks next wave. Same epoch.
2. Inside G_S but outside G_S^W (a region the workload never retained — only lightweight
   entry hooks, no rows) → TOPOLOGY_DIVERGENCE of the "retained set must grow" kind: new
   epoch, the region is added to the retained set, INSTRUMENT runs again for it, replay
   resumes. The membership test is the static candidate graph ∩ observed activation.
3. Outside G_S → unobserved, ignored (a static-slice gap if it ever mattered).
