---
name: lineage-identity-idea
description: Owner idea (2026-09-14): match replays by request LINEAGE (parent occurrence → thread/daemon → rpc), i.e. identity = recursive causal ancestry with k local to the parent; the anchor's lineage closure defines the slice. Deferred until the six cases pass.
metadata:
  type: project
---

Owner comment 2026-09-14 (verbatim gist): tracing work is fundamentally lineage; compare lineages instead of source+root. "datanode x → thread z → rpc" and "datanode x → rpc" are different request lineages; what we want is a replay that satisfies the causal-graph closure.

Planner assessment: today's identity (OccurrenceAddress = node, epoch, region, request family @source/api, k) is a depth-1 lineage whose "source" is a NODE. The generalisation: source = the PARENT OCCURRENCE address (recursively), k = k-th child of that parent with that api; timer/daemon-originated requests get their own lineage root (tick #k, local). Matching = isomorphism of the anchor's lineage closure; the linked replay's slice = that closure by construction (so a timer refresh outside the closure is DIAGNOSTIC by definition — exactly the 17897 NO_ACTIVE_REGION case). Runtime already propagates request scope across threads/async (RuntimeTraceContext, captureAsync, Thread.start arm), so the lineage is the chain of scopes; where scope is lost the address degrades to node level with an explicit row (fail-closed).

**Why:** ordinals shift when a flip inserts unrelated requests; a parent-local k is stable; lineage separates daemon-originated from request-originated occurrences.
**How to apply:** identity v2 after the six cases pass; broad change (OccurrenceAddress recursive; scheduler, composer, run_engine consumers). See [[graphchecker-core-design-principle]], [[handoff-family-phase2]].
