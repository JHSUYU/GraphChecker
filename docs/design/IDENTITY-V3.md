# IDENTITY-V3 — hierarchical causal execution index (owner's design, 2026-09-15)

Supersedes IDENTITY-V2's "lineage + per-hop k". The core challenge is cross-replay
occurrence correspondence under branch-flip perturbation: which dynamic occurrence in a
replay is the causal graph's node. Flat ordinals (`foo#17`, `k-th activation under the
parent`) shift whenever an unrelated extra invocation is inserted. Two mature techniques
are borrowed:
- Execution Indexing (Xin, Sumner, Zhang, PLDI 2008) / Precise Execution Point IDs
  (PEPID, ASE 2013): identify an execution point by its dynamic CONTROL CONTEXT (call-site
  path + loop-iteration context) so points correspond across re-executions.
- Distributed tracing structure (parent span → child span), but with the RANDOM span id
  replaced by a structural causal anchor.

## 1. The identity

```
OccurrenceId = TopologyEpoch
             + LogicalComponent          (node id, e.g. hdfs-17897/dn0)
             + StaticRegionId            (REGION.x — static code)
             + CausalContext             (why this occurrence ran)
             + LocalExecutionIndex       (where in the component's control structure)
```

CausalContext, one of:
- `Anchor(producerEndpointId, rpcStaticSite)` — the occurrence was started by a message:
  the incoming causal anchor = the PRODUCER's occurrence + the RPC static site + the
  producer's local execution index of the export (all inside the producer Endpoint id).
  Recursive: the producer's occurrence carries its own CausalContext.
- `Root(role, windowIndex)` — a workload action or a daemon tick with no incoming message
  (CLIENT, HEARTBEAT_TICK, KEY_MANAGER_TICK, BP_SERVICE_ACTOR …); windowIndex = the k-th
  such root inside the recording window (inherent ordinal, local to the role).
- `Lost(role)` — scope unattributable (`lineageLost`): degraded, still an identity.

LocalExecutionIndex (PEPID-style): the path from the scope root frame to the region entry
as a list of Frame(callSiteId, iteration), where callSiteId is the static call site
(class#method#bci) and iteration is the innermost enclosing loop's iteration count at
that frame (0 when not in a loop). An unrelated extra call elsewhere does not move it; an
extra iteration of a loop on the path does (inherent).

Endpoint keeps (occurrence, site, ordinal, attempt) with `ordinal` replaced by a
site-local execution index: SiteIndex = Frames from the region entry to the site (same
Frame form). Interaction = (kind, producer Endpoint, consumer Endpoint) unchanged.

Correspondence rule: two occurrences (or endpoints) in different replays are THE SAME iff
their ids are equal — component, region, causal context (recursively) and execution index
all equal. Nothing else (thread ids, object addresses, handles, session counters) enters
the id.

## 2. Case declarations (selectors)

Humans do not write execution indexes. A case declares a SELECTOR in the v1 spelling
(`node#epoch/region/REGION.x@src#epoch/api#k` or `node#epoch/region/REGION.x#k`); the
scheduler resolves it against the SEED session's occurrences: region equal, incoming
anchor's rpcStaticSite api equal (when given), k-th match in seed order → the full
OccurrenceId. The resolved id is published in the manifest; exploration and composition
use ids only.

## 3. Runtime computation (M2)

At region activation: CausalContext from the scope frame (the attach that started this
request → its producer Endpoint id; else the daemon/workload root role + window counter;
else Lost); LocalExecutionIndex from the invocation tree (RuntimeTraceContext parent
chain: call-site ids) plus loop-iteration counters (LOOPOWN already tracks loop bodies
per invocation). At every export/attach/write/read: SiteIndex from the region entry.
Publish on ActivationRow (the id and its parts) and on every Endpoint.

## 4. What changes in the contract (v2.0)

- `OccurrenceAddress` = (NodeId node, String regionId, CausalContext context,
  ExecutionIndex index, boolean lineageLost); `id()` = sha16 over the canonical render;
  `render()` = `node#epochN/region/REGION.x/ctx:<Anchor:<producerEndpointId>@<site> |
  Root:<ROLE>#<w> | Lost:<ROLE>>/idx:<callSite@iter>/.../`.
  `parseSelector(String v1)` returns a Selector (region, api?, k), not an address.
- `ExecutionIndex` = List<Frame(String callSiteId, int iteration)>.
- `Endpoint` = (OccurrenceAddress occurrence, String site, ExecutionIndex siteIndex,
  int attempt).
- `LineageHop`/`Role` list stays for Root/Lost contexts; the lineage LIST is gone.
- Rows unchanged otherwise. Explore/compose use ids and equality only.

## 5. Shared-state identity — Memory Indexing (owner, 2026-09-15)

Borrow Memory Indexing (Sumner & Zhang, FSE 2010: canonicalizing addresses across
executions): an object's canonical index is the execution index of its ALLOCATION, so
the same semantic object gets the same index in every replay regardless of its address.
In our terms:
- `LocationId.owner` for a heap object = the allocation Endpoint id: (allocating
  occurrence, allocation site `class#method#bci:NEW`, site-local ExecutionIndex) — never
  a session rid or an address. Arrays likewise (site `:NEWARRAY`). Static fields: the
  class.
- A shared-state access endpoint = (accessing occurrence, access site, site-local
  ExecutionIndex); a STATE interaction = (writer endpoint, reader endpoint) with the
  version pairing them within a run — the writer/reader endpoints are canonical across
  runs by construction, so the join needs no version-number alignment across sessions.
- Objects allocated before the recording window (pre-existing keys) get owner =
  `Root(WINDOW_START)#<class>#<m>` — a named degraded form, not an address.
The technique chain: local control occurrence → Execution Indexing/PEPID; RPC identity →
causal anchor (producer occurrence + call site + execution index); shared-state identity
→ Memory Indexing (allocation index) + field + access execution index.
