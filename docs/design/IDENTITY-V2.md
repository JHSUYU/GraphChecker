# IDENTITY-V2 — control lineage + data versions

Status: PLAN (owner asked 2026-09-14). Execute after the six cases pass on
identity v1 + the two joins (field-read join, gap-port join). Nothing here
adds a mechanism beyond the two identities; everything else is a consumer
change.

## 0. The two identities

| what | identity | today (v1) | v2 |
|---|---|---|---|
| a control occurrence (a call) | **lineage + per-hop k** | (node, epoch, region, family@source-node/api, k) — depth-1 lineage whose source is a node | `node#epoch / root-role#k / role@api#k / … / region#k` — each hop = (scope role, api, k among the parent's children of that role+api) |
| a data edge (which write a read saw) | **(location, version, writer occurrence)** | write log has (location, version, expression); read joins by observedVersion (being wired at link 4 now) | unchanged shape; location made replay-stable (§4) |

A lineage is a TYPE. Two calls with the same lineage are two instances; the
per-hop k separates them. The write→read relation between them is NOT a
lineage fact: it is the version of the location. Never identify a data edge
by the caller's lineage, never identify a call by the value it carried.

Roles are scope KINDS (client action, IPC handler, DataXceiver op,
BPServiceActor tick, KeyManager tick, executor task) — never thread ids.

Root hops: workload actions (k-th such action inside the recording window)
and daemon ticks (k-th tick inside the window). Daemon k stays a raw ordinal;
the closure (§3) makes that harmless: a daemon delivery the anchor never
reads is outside the closure by construction, and one it does read is
identified by the version it wrote, not by k.

## 1. Runtime: lineage on every activation (rows only)

- `RuntimeTraceContext` scope gains `parent` and `role`; async/thread
  handoff already carries scope (captureAsync, Thread.start arm) — add the
  IPC `Server.Call` enqueue/dequeue carry (Handler threads take calls from a
  queue; scope must be attached at enqueue and restored at dequeue) and the
  timer/daemon roots.
- `OccurrenceMinter` mints the v2 address by walking the scope chain; k per
  hop from a per-parent counter keyed by (role, api).
- Every activation row states its v2 address. Where a hop cannot be
  attributed the row states `lineageLost=true` and the address degrades to
  the v1 node-level form — fail-closed, never guessed.
- Measurement gate for this phase: on the six recordings, the share of
  activations with a complete lineage, per Hadoop entry point.

## 2. Addresses: v2 everywhere v1 is used

- Handoff phase ids: v_H = (consumer v2 address, port, k-th attach); e_p =
  (producer v2 address, port, k). Family join unchanged (wire pairing).
- Every declared port mints on reception regardless of selection (the
  "entry rule"); selection decides participation in COMPOSE only. That
  deletes RPC_HANDOFF_NO_ACTIVE_REGION.
- `target_occurrence` accepts a lineage path; a v1 full address is a valid
  depth-1 lineage and keeps working.
- Equality gate: on the six corpora every v1 occurrence maps to exactly one
  v2 address (bijection table published as a report, not a test).

## 3. Slice = closure; divergence = closure comparison

- Linked replay task set for an anchor A = ancestors(A) ∪ producers of every
  v_H on A's admitted paths (transitively) ∪ writers of every version A's
  π/φ read (from the recorded write log). Everything else runs concretely.
  This replaces the per-task slice heuristics.
- After a replay: compare A's closure tree with the plan's. Same
  (role, api, k) at every hop and every read version's writer inside the
  closure → matched. Extra children outside the closure → ignored
  (DIAGNOSTIC row). Missing hop, or a read whose observed version's writer
  is outside the closure → divergence → new epoch, re-planned from the new
  tree. RPC_HANDOFF_MISSING_METADATA becomes "consumer outside closure",
  DIAGNOSTIC by definition.
- The causal graph is then exactly: lineage edges + version edges. Iterative
  construction = merging trees per epoch. No other edge kind.

## 4. Replay-stable locations (only where φ reads instance fields)

- Static fields / singletons: location = (class, field) — already stable.
- Instance fields of objects allocated inside the closure (BlockKey):
  object id = (allocating occurrence v2 address, allocation site, m-th
  allocation there). The write log keys locations by that id so paths from
  different replays align on "the same BlockKey".
- Objects allocated outside the closure that the anchor reads: refuse with
  the location named (the case must declare a root at the source).

## 5. Order, gates, cost

| phase | change | gate |
|---|---|---|
| 0 (now) | six cases on v1 + field-read join + gap-port join | six verdicts |
| 1 | §1 rows only | lineage-complete share per entry point; no consumer change |
| 2 | §2 addresses | v1↔v2 bijection on six corpora; 17897 + bug3 lanes green |
| 3 | §3 closure | 17897's timer refreshes produce zero gaps by construction; a forced topology flip opens one epoch |
| 4 | §4 locations | bug3's BlockKey reads align across replays without concreteOwner heuristics |

Tests stay under the cap (fold into OccurrenceAddress, HandoffMint, Composer
tests). Size: addresses hashed with a side table; strings only in reports.

Risks: scope loss in IPC handler pools and Netty (phase-1 measurement
decides how much of §2 is reachable); daemon-root ordinals (mitigated by
§3); the object-identity rule in §4 is the one genuinely new definition.
