# CONTRACT-SPEC — the exact Java surface every Design 3 module codes against

Package `edu.uva.liftlab.graphchecker.d3.contract` (new; the old `contract/` and the
superseded `concolic/` types are deleted by step D). All types are immutable value
classes with a Gson-friendly shape (public final fields or records-style getters —
pick ONE style: plain final classes with a static `of(...)` factory and `equals/
hashCode/toString`; no Lombok). Ids are lowercase hex sha256 truncated to 16 chars
unless stated. Every row carries `sessionId` (the replay session that produced it).

## 1. Identity
- `NodeId(String node, int epoch)` — render `node#epoch<N>` e.g. `hdfs-17897/dn0#epoch0`.
- `LineageHop(Role role, String api /*nullable*/, int k)` — render `ROLE[@api]#k`.
  `enum Role { CLIENT, IPC_HANDLER, DATA_XCEIVER, HEARTBEAT_TICK, KEY_MANAGER_TICK,
  BP_SERVICE_ACTOR, SPS, BALANCER, EXECUTOR_TASK, REQUEST /*v1 depth-1*/, UNKNOWN }`.
- `OccurrenceAddress(NodeId node, List<LineageHop> lineage, String regionId, int k,
  boolean lineageLost)` — render `node#epochN/hop/.../region/REGION.x#k`; static
  `parse(String)` accepts BOTH the v2 render and the v1 case-declaration spelling
  `node#epochN/region/REGION.x@src#epochM/api#k` (→ one hop `REQUEST@src/api#k`) and
  `node#epochN/region/REGION.x#k` (→ empty lineage). `id()` = sha16(render).
- `Endpoint(OccurrenceAddress occurrence, String site, int ordinal, int attempt)` —
  `site` is the declared port id for WIRE (e.g. `XCH.<uuid>.resp.block-key-id`) or
  `<class>#<method>#<bci>:<READ|WRITE>` for STATE; `ordinal` = k-th event of that site
  inside the occurrence (1-based); `attempt` = retry number (0 when none). `id()`.
- `enum InteractionKind { WIRE, STATE }`.
- `Interaction(InteractionKind kind, Endpoint producer, Endpoint consumer)` — `id()` =
  sha16(kind + producer.id + consumer.id). `producerDegraded()` = producer.occurrence
  .lineageLost.
- `LocationId(LocationKind kind, String owner, String slot)` — `enum LocationKind
  { STATIC, INSTANCE, ARRAY, MAP }`; `owner` = class name for STATIC, or
  `<allocating Endpoint id>#<m>` (m-th allocation at that site in that occurrence) for
  heap objects; `slot` = field name/offset, index, or map key hash.

## 2. Rows (one JSONL file per kind under the session directory)
- `ActivationRow(sessionId, OccurrenceAddress occurrence, String taskId, boolean focused)`
- `DecisionRow(sessionId, occurrence, String siteId, int ordinal, boolean outcome,
  String term /*the branch PREDICATE as written at the site, polarity-free, SMT-LIB over
  declared symbols*/, Map<String,Long> clockReadings)` — RULING 2026-09-15: π conjunct =
  `outcome ? term : (not term)`; every consumer (composer π_p, Arms π_q, explore prefix)
  applies the outcome; the runtime never pre-applies it.
- `ExportRow(sessionId, Endpoint endpoint, String expressionRef, long handle,
  String recordedValue)`
- `AttachRow(sessionId, Endpoint endpoint, String symbol /*v_H*/, String arrival,
  boolean answered, String answeredValue /*nullable*/, Endpoint producer /*nullable
  when unpaired*/, String correlationId)`
- `WriteRow(sessionId, Endpoint endpoint, LocationId location, long version,
  String expressionRef)`
- `ReadRow(sessionId, Endpoint endpoint, LocationId location, long observedVersion
  /*-1 unknown*/, String symbol, String concreteValue /*nullable*/)` — `concreteValue`
  is what the read returned (`ReadRow.returned`): a scalar's literal, a String as its
  JSON string literal, null as `N`; absent for an identity.  A read joins its write
  if that lowers with no refusal, else its version's mint, and only then pins to it;
  a join that refused is the path's refusal only when nothing binds the read.
- `RootMintRow(sessionId, occurrence, String rootId, String symbol, RootKind kind,
  String recordedValue, String domainMin /*resolved absolute, nullable*/, String
  domainMax, boolean declared)` — `enum RootKind { MARKER, INTEGRAL, CLOCK }`.
- `TargetRow(sessionId, occurrence, String anchorSiteId, String phiTerm /*FATAL
  polarity always*/, boolean observedFatal, boolean reachedAnchor)`
- `GapRow(sessionId, GapKind kind, GapClass cls, String subject, String detail)` —
  `enum GapKind { ADMISSION_GAP, TOPOLOGY_DIVERGENCE, UNATTESTED_ARM, UNSTATED_VALUE,
  UNPRODUCIBLE_ANSWER, FORMULA_SAT_AT_RECORDED_VALUATION, DECLARATION_MISSING,
  LINEAGE_LOST }`, `enum GapClass { BLOCKING, DIAGNOSTIC }`.
- `ExpressionTable` — per session `expressions.jsonl` (`SessionExpressionLog`), appended as
  the replay files each expression: a header line, then each expression node once, children
  first, a child named by its session-local node number, and one line per ref naming its node
  (read back shared).  A ref is `EXPR.` + the 16 hex of a 64-bit Merkle hash over the
  expression DAG (`ExpressionRefs`: member names sorted, scalars' text, children's hashes), so
  equal expressions have equal refs in every session.  No SHA-256 in the replay: the concolic
  interpreter spent 2.1 ms a node on it.
- `SessionDir` — layout helper: `activations.jsonl, decisions.jsonl, exports.jsonl,
  attaches.jsonl, writes.jsonl, reads.jsonl, roots.jsonl, targets.jsonl, gaps.jsonl,
  expressions.jsonl` under `<iteration>/sessions/<sessionId>/`; `RowCodec` (Gson)
  reads/writes each kind; readers must never need to parse another kind's file.

## 3. Exploration contract (`d3.explore` writes, runtime reads)
- `Task(String taskId, OccurrenceAddress focused, List<OccurrenceAddress> factor
  /*state-connected co-occurrences, may be empty*/, String seedSessionId)`
- `Obligation(String obligationId, String taskId, String pathId, String siteId, int
  ordinal, boolean flippedOutcome, Map<String,String> rootAssignments, Map<String,
  String> answers /*attach Endpoint id → value*/, List<String> unproducible /*attach
  endpoint ids answered without an arm*/)` — the runtime applies `rootAssignments` at
  the mints and `answers` at the attaches of the focused occurrence.
- `Verdict enum { SAT_MODEL_READY, UNSAT, VALIDATED, NOT_ADMITTED, DIVERGED }` with
  `ObligationResult(obligationId, verdict, String sessionId /*of the replay*/, detail)`.

## 4. Composition contract (`d3.compose` writes)
- `Arm(String producerPathId, String piRef, String expressionRef, Set<String>
  guardRoots, boolean attested)`
- `Family(String interactionId, List<Arm> arms)`
- `PathEntry(String pathId, String sessionId, String selector, boolean fatalObserved)`
- `RootDomain(String rootId, RootKind kind, String recordedValue, String min, String
  max)`
- `enum ClaimKind { MARKER_FLIPPED, CLOCK_SKEW, MESSAGE_PAIRING_FLIPPED,
  RECORDED_FAILURE_EXPLAINED, NO_SUPPORTED_WITNESS }`
- `Claim(ClaimKind kind, int valuationOrdinal, Map<String,String> movedRoots,
  boolean polarityDecides, List<GapRow> gaps)`
- `CompositionManifest(OccurrenceAddress anchor, List<PathEntry> paths,
  List<Family> families, List<RootDomain> roots, int valuations, Claim claim,
  String smt2Path)`

## 5. Rules every module obeys
- Identity is by Endpoint/Interaction only; no request-family strings anywhere.
- φ is published in the fatal polarity by the runtime (TargetRow.phiTerm); the
  composer never re-derives polarity.
- One expression lowering (`d3.compose.SmtLowering`) used by the composer AND the
  flip solver; field projections: join to the observed write version, else pin to the
  concrete value, else UNSTATED_VALUE (refuse, naming it).
- No global assertion about a per-session fact: arrivals, clock readings and
  valuations are stated inside the path's own conjunction.
- Roots: declared domains relative to the recorded value (resolved absolute in
  RootMintRow); a root without a domain is pinned everywhere (composer and flip solver).
- Clocks: unbounded, `>= 0` floor only, per path.
- Tests are written AFTER the module compiles and runs on a corpus; folded into few
  test classes; whole suite ≤ 80 @Test.
