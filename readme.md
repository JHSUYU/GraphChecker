# Codex Task Document: General Causynth Prototype over Java Distributed Systems

## 0. Goal

Implement a general prototype named **Causynth** for analyzing distributed-system bugs from a local condition.

The tool should start from a local predicate in implementation code, such as:

```text id="n2s0q2"
map.get(k) == null
cacheEntry == stale
epoch mismatch
leader mismatch
membership missing
token/key invalid
lease expired
```

Then it should automatically build a causal transition graph by combining:

```text id="ltdh04"
1. static analysis over source/bytecode,
2. selective dynamic traces from unit tests,
3. unit-test event-schema merging,
4. boundary-effect modeling for RPC, restart, failover, time, timeout, crash,
5. causal-graph construction,
6. bad-condition satisfiability checking,
7. missing repair-edge detection.
```

The prototype will initially be developed on HDFS source code using Soot, but the implementation must be **target-agnostic**. HDFS-specific logic should live in a separate target configuration/specification file, not in the core analysis engine.

---

# 1. Core Research Idea

Most distributed failures eventually surface as a local condition inside one process:

```text id="kphy07"
receiver does not have key k
server rejects stale epoch e
node no longer recognizes member m
replica rejects old leader l
cache lookup returns invalid entry x
```

Causynth should treat that local condition as the seed and synthesize a distributed causal graph explaining how state across components, threads, RPCs, restarts, failovers, and time could make that local condition true.

The tool should also detect a general bug pattern:

```text id="wy0ddt"
A downstream failure signal proves that an upstream cached/state value is stale,
but the implementation does not causally invalidate or refresh that upstream state before reuse.
```

This is a **missing repair edge**.

General shape:

```text id="wruvzx"
CachedState[x]
  -> Use(x)
  -> DownstreamRejects(x)
  -> FailureSignal(x)
  -> no invalidate/update CachedState[x]
  -> LaterUse(x)
```

Required repair edge:

```text id="r06h3l"
FailureSignal(x)
  -> invalidate/update CachedState[x]
  -> retry or re-resolve state
```

Examples across systems:

```text id="0e68hq"
InvalidKeyException(k)
  -> clear cached key

NotLeaderException(newLeader)
  -> update cached leader

EpochMismatchException(newEpoch)
  -> refresh local epoch

UnknownMemberException(member)
  -> refresh membership view

LeaseExpiredException(lease)
  -> reacquire lease

TokenInvalidException(token)
  -> refresh token
```

---

# 2. Architecture Overview

The system should be split into a target-agnostic core and per-system target specs.

```text id="mm5tit"
causynth-core/
  IR
  static analysis framework
  dynamic trace format
  trace lifting
  unit-test schema merge
  boundary-effect library
  causal graph builder
  query engine
  repair-edge checker

targets/
  hdfs/
    target.yaml
    seed_patterns.yaml
    role_inference.yaml
    test_selection.yaml
    boundary_hints.yaml
```

The HDFS target is the initial case study, but the core should also work for future Java systems such as Cassandra, HBase, YARN, Kafka-like systems, or any large Java distributed system.

---

# 3. Inputs and Outputs

## 3.1 Inputs

```text id="eazcof"
1. Java source/bytecode repository
2. compiled classes and test classes
3. unit tests
4. target specification file
5. local condition seed
6. optional known exception/failure signal
7. generic boundary-effect library
8. optional LLM/manual hints
```

## 3.2 Outputs

```text id="pc935h"
causynth-output/
  target_resolved.json
  seeds.json
  static_cells.jsonl
  static_events.jsonl
  static_slices.json
  selected_tests.json
  dynamic_trace.jsonl
  lifted_schemas.jsonl
  merged_graph.json
  bad_condition_query.smt2
  witness.json
  repair_edge_report.md
  replay_plan.md
```

---

# 4. Target Specification

Do not hard-code HDFS-specific class names in the core. Use target specification files.

Example target spec:

```yaml id="epn0s4"
target:
  name: hdfs
  language: java
  repo_env: HDFS_REPO

local_conditions:
  - name: missing_map_entry
    pattern: "Map.get(key) == null"
    semantic_role: "receiver_missing_state"

failure_signals:
  - exception: "org.apache.hadoop.hdfs.protocol.datatransfer.InvalidEncryptionKeyException"
    payload_vars: ["keyId"]
    means: "receiver lacks state for keyId"

state_patterns:
  - name: key_membership_map
    class_contains: "BlockTokenSecretManager"
    field_names: ["allKeys"]
    abstract_as: "KeyRegistry[owner][key]"

producer_patterns:
  - name: cached_data_encryption_key
    class_contains: "KeyManager"
    field_names: ["encryptionKey"]
    abstract_as: "ClientCache[client].cachedKey"

repair_patterns:
  - name: clear_cached_key
    method_names: ["clearDataEncryptionKey", "clear", "invalidate"]
    writes: ["ClientCache[client].cachedKey"]
  - name: regenerate_key
    method_names: ["generateDataEncryptionKey", "newDataEncryptionKey"]
    writes: ["ClientCache[client].cachedKey"]

boundary_patterns:
  rpc:
    method_name_patterns: ["get*", "send*", "call*", "invoke*"]
    framework_hints: ["protobuf", "ipc", "netty", "hadoop rpc"]
  restart:
    method_name_patterns: ["restart*", "shutdown*", "start*", "stop*"]
  failover:
    method_name_patterns: ["transitionToActive", "transitionToStandby", "failover*"]
  time:
    method_name_patterns: ["now", "monotonicNow", "currentTimeMillis"]

test_selection:
  include_name_patterns:
    - "Key"
    - "Token"
    - "Encrypted"
    - "Failover"
    - "Restart"
    - "Balancer"
```

The target spec should be permissive and extensible. Unknown patterns should be represented as low-confidence events rather than ignored.

---

# 5. Core Intermediate Representation

The central IR is a **typed causal transition hypergraph**.

```text id="0mdrpg"
G = (C, E, P, H, O, Φ)

C: state cells
E: event schemas
P: boundary ports
H: order/read-from/time constraints
O: repair obligations
Φ: symbolic effects / formulas
```

---

## 5.1 StateCell

A `StateCell` is an abstract location:

```json id="bxj59b"
{
  "id": "Role[r].Component.field[index]@epoch",
  "role": "Role",
  "instanceParam": "r",
  "component": "Component",
  "path": "field/path",
  "indexParam": "optional symbolic key",
  "epochParam": "optional epoch",
  "valueType": "Bool|Object|Id|Epoch|Time|Role|Unknown",
  "evidence": []
}
```

Examples:

```text id="vu8mds"
Client[c].Cache.entry[x]
Server[s].Registry.member[x]
Replica[r].epoch
Group[g].leader
Node[n].alive
RPC[p].outcome
Time.now
```

Important: for any number of instances, use symbolic instance parameters:

```text id="m1r0l8"
Node[n]
Replica[r]
DataNode[d]
NameNode[nn]
Client[c]
Worker[w]
```

Do not enumerate all concrete instances unless a witness requires them.

---

## 5.2 EventSchema

An `EventSchema` is a parameterized transition:

```json id="q5npso"
{
  "id": "schema-id",
  "kind": "method|rpc|message|exception|restart|failover|time|repair|cache|map|timer|thread",
  "name": "HumanReadableName",
  "method": "optional fully qualified method",
  "callsite": "optional file:line",
  "roleParams": ["c", "s", "x"],
  "reads": ["StateCell ids"],
  "writes": ["StateCell ids"],
  "guards": ["formula strings"],
  "effects": ["formula strings"],
  "throws": ["exception type names"],
  "ports": ["boundary port ids"],
  "evidence": []
}
```

Examples:

```text id="8xnn0i"
UseCachedState(c, x):
  reads Client[c].Cache.entry[x]
  writes Request.payload[x]

RejectStaleState(s, x):
  reads Server[s].Registry.entry[x]
  guard Server[s].Registry.entry[x] == false
  writes Exception.StaleState(x)

HandleException(c, x):
  reads Exception.StaleState(x)
  writes none to Client[c].Cache.entry[x]
```

---

## 5.3 BoundaryPort

Boundary ports represent external or distributed effects:

```json id="b79aj2"
{
  "id": "rpc:Client->Service:method",
  "kind": "rpc|message|clock|restart|failover|thread|filesystem|network",
  "clientRole": "Client",
  "serverRole": "Server",
  "serviceGroup": "optional group",
  "method": "method name",
  "callsite": "file:line",
  "argTags": [],
  "returnTags": [],
  "possibleOutcomes": ["Return", "ThrowBeforeExec", "ThrowAfterExec", "Timeout", "Retry"]
}
```

---

# 6. What to Trace Dynamically

Do not trace everything. Trace only semantic events relevant to causal graph construction.

The dynamic tracer should emit JSONL `TraceEvent`s.

## 6.1 Object and Role Context

Trace:

```text id="rtis0y"
allocation site
class name
constructor arguments
ownership path
process/node id if available
thread id
service role
test name
configuration
```

Purpose:

```text id="iyscna"
concrete object -> abstract role
```

Example:

```text id="zkvixn"
object o17 of class ReplicaServer
  -> Replica[r]

object o31 of class ClientCache
  -> Client[c].Cache
```

---

## 6.2 State Access

Trace slice-relevant state operations:

```text id="g6yca7"
field read/write
Map.get / put / remove
Set.add / remove / contains
Queue.enqueue / dequeue
cache get / put / invalidate
AtomicReference get / set / compareAndSet
```

Abstract collection operations:

```text id="oc2li9"
Map.get(k)       -> read MapCell[k]
Map.put(k, v)    -> write MapCell[k] = v
Map.remove(k)    -> write MapCell[k] = null/false
Set.contains(k)  -> read SetCell[k]
Set.add(k)       -> write SetCell[k] = true
Set.remove(k)    -> write SetCell[k] = false
```

---

## 6.3 Branch Predicates

Trace branch predicates involving seed-relevant cells or values:

```text id="gwwulq"
cache.get(x) == null
epoch < currentEpoch
leader != localLeader
member not in membership
token.expiry < now
```

Record:

```text id="rsyuos"
condition expression
symbolic variables
branch outcome
source location
```

---

## 6.4 Value-Flow Tags

Trace abstract value propagation:

```text id="t56x61"
assignment
method argument
return value
serialization/deserialization
RPC payload
exception payload
log message payload if useful
```

Example:

```text id="6ny0xk"
Server[s].epoch -> Response.epoch -> Client[c].cachedEpoch
Client[c].cachedLeader -> Request.target -> Server[s]
```

---

## 6.5 Boundary Events

Trace:

```text id="ljytj8"
RPC call / return / exception / timeout
message send / receive
socket connect / read / write if visible
clock read
scheduled task firing
thread start
process/node start/stop/restart
role/failover/membership change
filesystem read/write if relevant
```

Boundary records should include:

```text id="jwibq9"
client role
server role or service group
method/port
callsite
argument tags
return tags
exception type
retry behavior if observed
```

---

## 6.6 Exception and Repair-Path Events

Trace:

```text id="91u5ea"
exception thrown
exception caught
catch block entered
state write inside catch
retry after catch
same value reused after catch
```

This is essential for missing repair-edge detection.

---

# 7. Static Analysis

Use Soot over Java bytecode / Jimple.

The static analysis should be target-agnostic and driven by the target spec.

## 7.1 Seed Finder

Find local conditions and failure signals:

```text id="fshn3j"
throw sites of target exceptions
catch sites
if conditions involving map/cache lookup failure
branch conditions involving stale epoch/leader/token/member
methods returning or producing state later used in the bad condition
```

Output:

```text id="gw8xry"
seeds.json
```

---

## 7.2 State Cell Extractor

From seed variables, extract candidate abstract cells:

```text id="065bp4"
fields
map entries
set membership
cache entries
object fields
atomic references
queues
role variables
```

Use the target spec to map concrete fields/classes into abstract cells.

---

## 7.3 Backward Slice from Local Condition

From local condition variables, find:

```text id="bj2mxd"
producers of key/value used in condition
writers to missing/invalid receiver state
sources of request payload
caches that hold the value
methods that update/clear/refresh state
boundary calls that fetch or transmit the state
```

---

## 7.4 Forward Slice from Failure Signal

From exception/error signal, find:

```text id="qcx6mh"
catch handlers
logging-only handlers
retry loops
state invalidation
state refresh
same-state reuse
propagation to caller
```

---

## 7.5 Static Repair-Edge Checker

For each candidate stale state cell `C` and failure signal `E(x)`:

```text id="v8gsag"
check whether every path from E(x) to a later reuse of C[x]
passes through a write that kills or refreshes C[x]
```

If not, emit a missing repair-edge candidate.

---

# 8. Event Lifting

Convert concrete dynamic trace into role-parameterized event schemas.

## 8.1 Role Lifting

Concrete objects become role parameters:

```text id="2uv2o7"
o17 -> Client[c]
o21 -> Server[s]
o31 -> Replica[r]
o41 -> Cache owned by Client[c]
```

Use:

```text id="co3ce6"
class name
ownership path
constructor/config
test fixture naming
thread/process role
target spec hints
```

---

## 8.2 Value Lifting

Concrete values become symbolic values:

```text id="7994gc"
1005215027 -> k
42 -> epoch_e
server3 -> leader_l
token-abc -> token_t
```

Preserve equalities and inequalities observed in the same trace.

---

## 8.3 Event Lifting

Concrete event:

```text id="sdaz2g"
client0.cache.get(leaderId)
```

Schema:

```text id="tc1ue6"
ReadCache(Client[c].Cache[leader])
```

Concrete event:

```text id="cfs1k8"
server2 throws NotLeaderException(newLeader = server3)
```

Schema:

```text id="2tmtcm"
RejectStaleLeader(Server[s], Leader[new]):
  writes Exception.NotLeader(new)
```

---

# 9. Unit-Test Merge

Unit tests are merged at the event-schema level, not at the concrete trace level.

## 9.1 Event Signature

Group schemas by:

```text id="fdn25d"
sig(schema) =
  <kind,
   method/callsite or boundary port,
   role pattern,
   read-cell pattern,
   write-cell pattern,
   effect pattern>
```

Do not merge solely by method name.

---

## 9.2 Merge Types

### Exact Merge

Same method/callsite and same read/write/effect pattern.

### Alpha-Equivalence Merge

Same structure modulo instance names.

```text id="2ce26u"
Replica[r1].epoch[e1]
Replica[r2].epoch[e2]

merge:
Replica[r].epoch[e]
```

### Conservative Anti-Unification

Different methods but same causal shape.

Example:

```text id="6td6nu"
ReadPath uses cached token.
WritePath uses cached token.
ReplicationPath uses cached token.

generalized schema:
UseCachedState(actor, operation, token)
```

Allow this only when:

```text id="3aao3t"
types are compatible
ownership is compatible
read/write cell pattern is compatible
effect formula is compatible
static dataflow supports the relation
```

---

## 9.3 Constraints to Preserve

During merge, preserve:

```text id="as7ndl"
type constraints:
  Client[c] != Server[s]

ownership constraints:
  Client[c].Cache != Server[s].Cache unless proven same role

protocol constraints:
  source != target
  oldLeader != newLeader
  oldPrimary != newPrimary

epoch constraints:
  state@epoch_i before state@epoch_j
  restart increments process epoch
  failover increments service epoch

value constraints:
  request.x == cached.x
  oldValue != newValue if observed or required
```

---

## 9.4 Causal Edge Construction

Add a causal edge when:

```text id="azdknt"
schema A writes state cell C
schema B reads state cell C
```

or:

```text id="0lljy1"
value tag from A flows into B
```

or:

```text id="4c5qla"
exception from A is caught by B
```

or:

```text id="ptyv3p"
boundary semantics connect them
```

Examples:

```text id="est6v4"
RPC call -> RPC return
restart -> init -> registration
failover -> active role resolution
timer -> scheduled updater
```

---

# 10. Boundary-Effect Library

Boundary effects should be first-class event schemas.

## 10.1 RPC Automaton

Represent RPC as:

```text id="gm1npq"
RPCPort(client, server/serviceGroup, method, callsite, args, retryPolicy)
```

Outcomes:

```text id="h61oi1"
Return(server, value)
ThrowBeforeExec(exception)
ThrowAfterExec(exception)
Timeout
Retry(nextServer)
```

For read-only RPC:

```text id="y04zd2"
Return:
  value = f(server.state)

Throw / Timeout:
  client follows exception CFG
  no return value assigned
  local state changes only if catch block writes it
```

For mutating RPC:

```text id="r38092"
ThrowBeforeExec:
  server effect absent

ThrowAfterExec:
  server effect may have happened

Timeout:
  server effect unknown unless protocol gives stronger semantics
```

---

## 10.2 Failover / Leader Change

```text id="04bhrl"
RoleChange(group, old, new):
  active(group) := new
  old != new
```

RPC resolution should read this active role:

```text id="n37so6"
Resolve(serviceGroup, active(group), retryPolicy)
```

---

## 10.3 Restart

```text id="kmzq3t"
Restart(process p):
  p.epoch++
  volatile cells reset
  persistent cells reload
  bootstrap / registration events enabled
```

---

## 10.4 Time

```text id="vd2b06"
TimeAdvance(dt):
  now_after = now_before + dt
  dt >= 0
```

Time affects:

```text id="vprv78"
expiry checks
leases
tokens
scheduled tasks
timeout
removeExpired
retry interval
```

---

# 11. Bad-Condition Query

The query should be target-agnostic.

General form:

```text id="is8y1f"
exists actor, receiver, x:
  Use(actor, x)
  AND ReceiverRejects(receiver, x)
```

Examples:

```text id="0amyod"
exists client, server, leader:
  client sends request to cachedLeader = leader
  server rejects leader as stale

exists sender, receiver, key:
  sender sends key
  receiver lacks key

exists replica, epoch:
  replica uses epoch
  coordinator rejects epoch as stale
```

The prototype can initially emit pseudo-SMT or SMT-LIB.

Output:

```text id="zy3rai"
bad_condition_query.smt2
witness.json
```

---

# 12. Missing Repair-Edge Detection

This is the main bug detector.

## 12.1 General Definition

Given:

```text id="fmrm89"
C[x] = upstream cached/state cell
Use(C[x]) = an event that sends/uses x
Reject(x) = downstream local condition proving x invalid
E(x) = failure signal carrying x
LaterUse(C[x]) = reuse of same stale state
```

Missing repair edge exists if:

```text id="xkwxi0"
SAT(
  Use(C[x])
  ∧ Reject(x)
  ∧ E(x)
  ∧ LaterUse(C[x])
  ∧ NoWriteTo(C[x]) between E(x) and LaterUse(C[x])
)
```

Required repair edge:

```text id="p7i6he"
E(x) -> kill/update/refresh C[x]
```

---

## 12.2 What Counts as Repair?

A repair edge is any state transition that invalidates or refreshes the stale producer before reuse:

```text id="z70gv4"
cache[x] := null
cache.invalidate(x)
cachedLeader := newLeader
epoch := responseEpoch
membership := refresh()
token := renew()
key := regenerate()
retry with newly resolved state
```

Repair patterns should be configurable in target spec.

---

# 13. LLM-Assisted Mode

Strict mode must work without an LLM.

LLM-assisted mode can propose:

```text id="kyb6u2"
semantic labels for state cells
candidate failure signals
candidate repair patterns
candidate boundary contracts
candidate tests to run
sibling paths with similar stale-state shape
```

But LLM output is only a hint. Every hint must pass:

```text id="8xpxw9"
type checking
static dataflow validation
trace validation if available
effect compatibility
SMT consistency
replay validation if a bug is reported
```

Implement LLM-assisted mode initially as optional hint files:

```text id="3s6b5w"
llm_hints/semantic_labels.json
llm_hints/repair_patterns.json
llm_hints/boundary_contracts.json
```

No runtime LLM API call is required.

---

# 14. CLI

Implement:

```bash id="qe7v2c"
java -jar causynth.jar \
  --repo "$TARGET_REPO" \
  --target-spec targets/hdfs/target.yaml \
  --classpath-file causynth-output/target.classpath \
  --output causynth-output \
  --mode all
```

Modes:

```text id="3st3y0"
static
trace
lift
merge
query
repair-check
all
```

---

# 15. Suggested File Structure

```text id="c6d7fe"
causynth/
  README.md
  pom.xml or build.gradle

  src/main/java/org/causynth/Main.java

  src/main/java/org/causynth/model/
    StateCell.java
    EventSchema.java
    BoundaryPort.java
    CausalEdge.java
    TraceEvent.java
    RepairObligation.java
    TargetSpec.java

  src/main/java/org/causynth/staticanalysis/
    SootSetup.java
    StaticSeedFinder.java
    StateCellExtractor.java
    BackwardSlicer.java
    ForwardExceptionSlicer.java
    StaticRepairEdgeChecker.java

  src/main/java/org/causynth/trace/
    TraceLogger.java
    TraceConfig.java
    TraceEventWriter.java
    TraceLifter.java
    RoleInferencer.java
    ValueTagger.java

  src/main/java/org/causynth/merge/
    EventSignature.java
    UnitTestSchemaMerger.java
    AntiUnifier.java
    ConstraintInferencer.java

  src/main/java/org/causynth/boundary/
    RpcAutomaton.java
    RoleChangeSchema.java
    RestartSchema.java
    TimeAdvanceSchema.java
    BoundaryEffectLibrary.java

  src/main/java/org/causynth/query/
    BadConditionQuery.java
    WitnessFinder.java
    SmtEmitter.java

  src/main/java/org/causynth/repair/
    RepairEdgeChecker.java
    RepairReportWriter.java

  targets/
    hdfs/
      target.yaml
      seed_patterns.yaml
      role_inference.yaml
      test_selection.yaml
      boundary_hints.yaml

  scripts/
    build_classpath.sh
    run_static_analysis.sh
    run_selected_tests_with_trace.sh
```

---

# 16. Development Order

Implement in this order:

```text id="on65cs"
1. TargetSpec parser.
2. Core IR classes and JSON output.
3. Soot setup and classpath script.
4. StaticSeedFinder driven by target spec.
5. StateCellExtractor.
6. BackwardSlicer.
7. ForwardExceptionSlicer.
8. StaticRepairEdgeChecker.
9. Initial repair_edge_report.md.
10. TraceLogger and JSONL trace format.
11. TraceLifter.
12. UnitTestSchemaMerger.
13. BoundaryEffectLibrary.
14. BadConditionQuery and SmtEmitter.
15. WitnessFinder.
16. Replay plan generator.
```

The first useful milestone is static-only:

```text id="s4mknj"
Given a target spec and local failure signal,
find candidate stale producer cells,
candidate downstream rejection sites,
and missing repair-edge candidates.
```

---

# 17. Acceptance Criteria

The prototype is acceptable if it can:

```text id="4l83wk"
1. Load a target spec.
2. Build or consume classpath for a Java system.
3. Find local-condition seeds and failure-signal sites.
4. Extract relevant state cells.
5. Build backward and forward slices.
6. Emit event schemas.
7. Merge schemas from at least two unit-test traces or static traces.
8. Add boundary-effect schemas for RPC, restart, failover/role-change, and time.
9. Emit a causal graph JSON.
10. Emit a bad-condition query.
11. Report missing repair-edge candidates.
12. Keep system-specific logic outside the core engine.
```

---

# 18. HDFS Should Be Only the First Target

HDFS target spec can instantiate the general framework with:

```text id="ca67h7"
failure signal:
  InvalidEncryptionKeyException

local condition:
  receiver key registry missing keyId

stale producer:
  cached DataEncryptionKey

repair:
  clear cached key / regenerate key / retry
```

But the core engine should remain general enough to support:

```text id="vq4d9m"
NotLeaderException -> update leader cache
EpochMismatch -> refresh epoch
UnknownMember -> refresh membership
LeaseExpired -> reacquire lease
TokenInvalid -> renew token
InvalidKey -> regenerate key
```

Do not name core classes after HDFS-specific concepts. Use generic names such as:

```text id="3jv4zj"
CachedState
ReceiverState
FailureSignal
RepairEdge
BoundaryPort
RoleChange
Restart
TimeAdvance
```
