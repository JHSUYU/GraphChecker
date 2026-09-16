# IDENTITY-IMPL — the identity, as one small implementation (binding for M1b/M2/M3/M4)

## A. Data (contract v2.0, package d3.contract)

```java
final class Frame { String callSite; int iteration; }         // class#method#bci, loop iter (0 = none)
final class ExecutionIndex { List<Frame> frames; String hash; } // hash = fold(frames), 16 hex
abstract class CausalContext {                                  // exactly three forms
  static Anchor of(String producerEndpointId, String rpcSite);  // started by a message
  static Root   of(Role role, int windowIndex);                 // workload action / daemon tick
  static Lost   of(Role role);                                  // scope unattributable
}
final class OccurrenceAddress { NodeId node; String regionId; CausalContext ctx; ExecutionIndex idx; }
  // id() = sha16(node.render + "/" + regionId + "/" + ctx.render + "/" + idx.hash)
final class Endpoint { OccurrenceAddress occ; String site; ExecutionIndex siteIdx; int attempt; }
  // id() = sha16(occ.id + "/" + site + "/" + siteIdx.hash + "/" + attempt)
final class Interaction { Kind kind; Endpoint producer, consumer; }   // id = sha16(kind, p.id, c.id)
final class LocationId { Kind kind; String owner; String slot; }
  // owner: STATIC → class; heap → allocation Endpoint id; pre-window → "preWindow:<class>#<m>"
final class Selector { String regionId; String api /*nullable*/; int k; }  // parsed from the v1 case string
```

## B. Runtime computation (M2) — one stack per thread, O(1) per event

```
ThreadState { Deque<Frame> stack; Map<invocation, int> loopIter; ScopeFrame scope; long seq; }

onMethodEnter(callSite):      stack.push(Frame(callSite, currentLoopIter()))   // EI paper's stack
onMethodExit():               stack.pop()
onLoopIteration(loopId):      loopIter[top invocation, loopId]++              // LOOPOWN's counter
scopeStart(kind, payload):    scope = { role, windowIndex = ++window[role], anchor = payload?.producerEndpointId, rpcSite }
                              // payload = the attach that carried the request in (its producer Endpoint), else null
scopeCarry(task/call/queue):  copy the ScopeFrame onto the child (Thread.start, executor, Server.Call enqueue→dequeue, SASL op lifetime)

regionEnter(regionId):
  ctx  = scope.anchor != null ? Anchor(scope.anchor, scope.rpcSite)
       : scope.role   != null ? Root(scope.role, scope.windowIndex)
       : Lost(roleGuess)
  idx  = ExecutionIndex(stack.frames from scope root to here)
  occ  = OccurrenceAddress(node, regionId, ctx, idx)
  regionBase = stack.size()                    // for site-local indexes
  publish ActivationRow(sessionId, occ, focused?)

siteEvent(site):              siteIdx = ExecutionIndex(stack.frames[regionBase..]) ; Endpoint(occ, site, siteIdx, attempt)
onAllocate(obj, site):        obj.shadow.owner = Endpoint(occ, site+":NEW", siteIdx).id   (Memory Indexing)
                              // objects seen with no shadow after window start: "preWindow:<class>#<m>"
onExport/onAttach/onWrite/onRead: rows with Endpoint (and LocationId.owner from the shadow), seq = ++seq
onAttach(msg):                producer = msg.header.producerEndpointId (carried on the wire, see C); if absent → producer Endpoint with ctx = Lost
```

Hash chain: `hash(frames) = fold(h, f) = sha16(h + "/" + f.callSite + "@" + f.iteration)`, maintained
incrementally on push/pop (keep a stack of prefix hashes), so ids are constant-size and comparable.

## C. What travels on the wire

Every declared port's message carries, beside the expression handle it already carries, the
producer Endpoint id (48 bytes) in the same header slot the correlation id uses. The
consumer's attach reads it → AttachRow.producer; the consumer's scopeStart uses it as the
Anchor. No random span ids; nothing else.

## D. Selector resolution (once per campaign, in PLAN)

```
resolve(Selector s, seedSession):
  cands = seed activations with regionId == s.regionId
  if s.api != null: cands = those whose ctx is Anchor and rpcSite api == s.api
  return cands.sortedBy(seq)[s.k - 1].occ.id        // k-th in seed order; error if absent
```
Published in the manifest as the anchor id; explore/compose use ids only.

## E. Correspondence and divergence (M3/M4)

same occurrence ⇔ id equal. same interaction ⇔ both endpoint ids equal.
Divergence (new epoch) ⇔ the anchor's closure gains an interaction pair not in the epoch
catalog, or an occurrence in the closure changes its CausalContext. An occurrence whose
ctx matches but whose idx differs only in loop iterations off the anchor's path is a
DIAGNOSTIC "index shifted" row, not a divergence (two-level matching: ctx primary, idx
secondary). Map entries are joined by (map owner, key expression), never by element rid.

## F. Size and cost
Contract: ~300 lines. Runtime: ~400 lines (stack + hashes + scope carry + allocation hook +
selector). Wire header: +48 bytes per declared-port message. Per event: one hash fold.
