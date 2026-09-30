# Identity: occurrences, contexts, doors, schedule

A causal graph node is one region occurrence `(r, c, i)`: the static region `r`, the causal context
`c` that started it, and the execution index `i` locating it in its component's control structure.
Recording and every replay compute it with the same function over the same woven hooks, so a node
of one run is the same node in another iff the ids are equal. Java paths below are under
`src/main/java/edu/uva/liftlab/graphchecker/`.

## 1. The occurrence address

`contract/OccurrenceAddress`:

```
<node>#epoch<N>/region/<regionId>/ctx:<CausalContext>/idx:<callSite>@<k>/<callSite>@<k>/...
id = sha16(node/regionId/context/index-hash)
```

- **node** (`contract/NodeId`): the logical component the work belongs to (§5) and its epoch; the
  epoch advances only when the workload calls `restartSource`.
- **r**: a `REGION.<hash>` skeleton id (`causynth/SymbolicRegionPlanner`, a region rooted at an
  execution-context entry: `MAIN_ENTRY`, `THREAD_ENTRY`, `TASK_ENTRY`, `COMMUNICATION_ENTRY`,
  `STATE_WRITER_ENTRY`, `EXPLICIT_FAULT_ENTRY`, `FAILURE_TARGET_ENTRY`), or `ROLE.<role>` for work
  under no region (`runtime/Identity#roleOccurrence`). Where a region's root runs a service loop the
  recording iterated more than once, one loop iteration is the activation (`LOOP_BODY_ROOT`,
  `causynth/StaticProgram#loopBodyRoot`).
- **c**, **i**: §2 and §3. Nothing else enters the id: no thread id, object address or run ordinal.

`runtime/Identity#occurrence` is the one computation, called at region entry in both passes;
offline stages read the address the recording stated (`runtime/RuntimeRegionPlanner#recordedNode`)
and never re-derive it.

**Fold rule** (`Identity#fold`): a declared region entered synchronously inside a running
occurrence opens none; its events belong to the running occurrence, and a marker region keeps the
region stack balanced. Exception: an occurrence opened with a `Lost` context absorbs nothing once
the thread has a context of its own. A thread boundary always ends an occurrence: a child thread
inherits region depth but no occurrence. PLAN records the folded regions on their owner
(`RuntimeRegionPlanner#stampFoldedRegionEntries`).

## 2. The causal context `c`

`contract/CausalContext`, exactly three forms:

| form | render | meaning |
|---|---|---|
| `Anchor(producerEndpointId, rpcSite)` | `Anchor:<endpointId>@<rpcSite>` | a message started it; the anchor is the sender's endpoint id (§4), recursively carrying the sender's own context |
| `Root(role, api, k)` | `Root:<ROLE>[/<api>]#<k>` | the k-th root of that (node, role, api) in the recording window: a workload request, a daemon tick, a service-loop turn |
| `Lost(role)` | `Lost:<ROLE>` | unattributable; still an identity |

`runtime/Lineage` keeps a per-thread stack of hops (role, api, k, root?, anchor). `Identity#here`
reads it: the innermost hop carrying an anchor, searched outwards and stopped at the innermost root
hop, gives `Anchor`; else the innermost root hop gives `Root` when its role is known and `k > 0`;
else `Lost` of the fallback role.

Hops are opened by (all in `runtime/RuntimeTraceContext`):

| opener | hop |
|---|---|
| `beginRequest` (the workload, `MessageDoors.beginRequest`/`beginWorkloadCall`) | role `CLIENT`, api = the request's name; a root where none stands, or always (`pushCallRoot`) for a workload call |
| `beginTick` (`MessageDoors.beginTick`) | a root of the given role, whatever the thread stands in (`pushRoot`) |
| `beginWake` (at the return of a timed wait, `runtime/WakeScopes`) | a root of role `WAKE`, api = `Class.method` of the wait; only on a thread attributed to a node and only when every open scope is itself a turn |
| `enterInbound` (a received message) | role = the transport, api = the request's `<source>/<api>`; the anchor is `Interactions.sender(transport, correlation, half)`, rpcSite `<TRANSPORT>[.<VIA>]/<api>` |
| `enterCarriedScope`, `claimCarried` (queued or started work) | the carried lineage restored, plus a nested hop (`EXECUTOR_TASK` for a claimed start) |

`k` counts root hops only, per (window, node, role, api), in one JVM-wide counter
(`Lineage#push`). A turn begun before the window has `k = 0` (`Lineage#rootWindowIndex`), so its
context is `Lost`; a request begun before the window keeps its `k`.

## 3. The execution index `i`

`contract/Frame` = (callSite, k), rendered `callSite@k`; `contract/ExecutionIndex` = a list of
frames with hash `fold(h, f) = sha16(h + "/" + f.callSite + "@" + f.iteration)`.

- **Frames.** Every application-scope method opens a level at entry and closes it at every exit,
  in both passes (`Identity#enterFrame`, `#exitFrame`). A frame's `k` is the k-th event at that
  site in the enclosing level under the current root hop (`State#nextSiteEvent`, keyed by level,
  root-hop token and site). It is not a loop-iteration count.
- **Start frames.** `Identity#startWork` files, per `Thread.start` or submission, a frame
  (site, k-th start at that site) with the carrier; the started work claims it at its first
  identity event or at its functional method's entry (`#claimStart`), so siblings started from one
  site differ by that frame alone. Claimed starts nest.
- **Scope base** (`Identity#scopeStart`, `Hop`): an occurrence's index starts at its context's
  origin: the inbound scope for `ANCHOR` (which pooled handler serves a request is scheduling, not
  identity), the scope start for `SCOPE_ROOT` (a request, a carried scope, a wake turn), the claimed
  start frame for `STARTED_ROOT` (a daemon tick).
- **Occurrence index** = frames from the scope base to the region entry (`#regionEnter`).
- **Window rule** (`runtime/RecordingWindow`): the workload opens the window
  (`MessageDoors.startRecording`) and may close it (`stopRecording`); every count restarts at the
  window, and a frame entered before it stands at `k = 0` in any address. Neither the trace nor the
  schedule states anything before the window opens.
- **Branch ordinals**: the 1-based count of decisions at one site in one occurrence, folded entries
  included (`#nextBranchOrdinal`), the key a flip is addressed by.

## 4. Endpoints and interactions

`contract/Endpoint` = (occurrence, site, siteIndex, attempt), `id = sha16(occurrence.id / site /
siteIndex.hash / attempt)`, rendered `<address>/site:<site>/sidx:<frames>/att:<n>`.

- `siteIndex` = frames from the innermost region's base, plus the event's own `(site, k)` frame
  (`Identity#endpointAt`). A VM-logged read or write gets the same shape after the fact
  (`runtime/LoggedEventSites#siteIndex`): the frames the region's frame journal
  (`runtime/FrameJournal`, keyed by the VM's region-enter event id) places it on, then `(site, k)`,
  `k` its rank by event id among the performing occurrence's logged events at that site on the
  same frames, counted over every logged event, published or not. The performer is the activation
  the VM states for the event, not the occurrence that read the log out.
- `site` is the port id (WIRE), `<class>#<method><descriptor>#<bci>:WRITE|READ` (STATE,
  `Endpoint#stateSite`), or `<transport>#<half>` for a whole message.
- The id is recursive through the Anchor chain: one unreproduced link anywhere upstream changes it.

**Message producers.** A sent message's producer endpoint is minted at the send
(`Identity#messageSent`) in the sender's current occurrence. A response's producer endpoint is
minted when its request is received (`Identity#responseEndpoint`: the request scope's role
occurrence, site `<transport>#RESPONSE`, index `[site@0]`), and the send reuses it
(`runtime/CausynthTraceRecorder` `RECEIPTS`), so whichever thread sends the response names the same
producer. Two messages carrying one producer endpoint are named as a `LINEAGE_LOST` DIAGNOSTIC row.

**Pairing** (`runtime/Interactions`, in-JVM, each store bounded to 8192 entries by eviction):
`sent` files a message's producer by (transport, correlation, half) and by endpoint id; a receiver's
anchor is looked up there. `exported` files a staged value's producer by VM handle and by
(correlation, port); `pairing` answers an attach by `HANDLE`, else `CORRELATION_PORT`, else
unpaired. The wire header does not carry the producer endpoint.

**Interactions** (`contract/Interaction`): (kind, producer endpoint, consumer endpoint), `id =
sha16(kind + producer.id + consumer.id)`, kind `WIRE` (export to attach, `AttachRow#interaction`)
or `STATE` (write to read, `smt/Arms#stateArms`). `smt/Arms` is the one arm rule for COMPOSE and
the flip solver:

- a WIRE interaction's arms are the producer endpoint's exports from runs whose own pairing named
  this consumer;
- a STATE read's arms are its observed writer plus every attested writer occurrence of the same
  session that is HB-concurrent with the reader (not the same thread, not an anchor-chain
  ancestor either way, both chains reaching a `Root`; a `Lost` context is never concurrent), one
  arm per writer occurrence: the observed writer's at the write the read observed, any other at
  its last write of the location. Locks are not constraints.
- an occurrence is attested in a session that has an instrumented activation row for it
  (`Arms#attested`); no witness may move a root inside an unattested arm.

**Locations** (`contract/LocationId`, `KIND/<owner>#<slot>`): the owner of a heap location is the
VM's per-run object id, a static field's owner its class. A state join is per session; there is no
cross-run object identity.

## 5. Attribution: which node

`runtime/Attribution#resolve`, three rules in order: the innermost explicit scope on the thread
(a request, a registered inbound owner, a tick owner); else the innermost frame whose receiver is a
registered object; else the node of whatever started this work (followed through starters, at most
32 deep). All three failing is `null`, never a guess: the activation then has no address, and an
activation under a `Lost` context keeps its degraded one; both are `LINEAGE_LOST` DIAGNOSTIC rows
(`runtime/RowRuntime#beginActivation`).

The system's test adapter registers nodes through `MessageDoors.registerNode` (anchor plus aliases:
the objects the node runs its work through), `registerSource`, `registerSourceAlias` and
`restartSource` (HDFS `CausynthCluster`, Solr `CausynthSolrCluster`, in the trees). Work on no
registered node is attributed to `workload/unregistered` (`RuntimeRegionPlanner.UNREGISTERED_SOURCE`).

PLAN refuses what the address cannot tell apart: activations of one region sharing one address are
`OCCURRENCE_ADDRESS_SHARED` (BLOCKING when the region is in the published closure,
`causynth/RuntimeSelectedRegionFinalizer`), and a plan row whose causal anchor or source names
another node than its address is `TASK_UNANSWERED` BLOCKING
(`RuntimeRegionPlanner#stateAnchorOffAddress`).

## 6. Carrying context across threads

`plan/WorkStartSites` is the one list of shapes, read by the weave and by `plan/LineageScan`:

| shape | calls |
|---|---|
| receiver starts | `Thread.start()`, `ForkJoinTask.fork()`/`invoke()` |
| submissions | `execute`, `submit`, `schedule`, `invokeAll` with a `Runnable`, `Callable`, `ForkJoinTask` or `Collection` (one start per element) argument |
| queue submissions and claims | `BlockingQueue` `put`/`offer`/`add` (and deque ends); `take`/`poll` (and deque ends) return the work |
| work entries (where a start is claimed) | `Runnable.run`, `Callable.call`, `ForkJoinTask.exec`/`compute`, `Thread.run` |
| timed waits | `Thread.sleep`, `TimeUnit.sleep`, `Object.wait(long)`, `LockSupport.parkNanos`, `Condition.awaitNanos`/`await(long, TimeUnit)`, `BlockingQueue.poll(long, TimeUnit)`; notifiers and untimed waits as signal state |

A start captures the starter's scope with the carrier (`RuntimeTraceContext#captureAsync`) and
writes a `START` event; the claim restores it (`RuntimeTraceContext#claimCarried`) and writes a
`CLAIM` event. A pool's own worker thread
inherits no scope (`runtime/PoolWorkers`: `ThreadPoolExecutor.addWorker`,
`ForkJoinPool.createWorker`, Jetty `QueuedThreadPool.startThread`); each task carries its own.

The lineage scope (`plan/LineageScan`, run by `run_engine.sh campaign_lineage_classes` over
`causynth_lineage_roots`) weaves the start, claim and timed-wait hooks into every class of the
system's own class roots that starts, hands off, runs or waits, whether or not the case analyses
it.

## 7. Doors

### 7.1 Message doors

`runtime/MessageDoors` is the transport-neutral API every system's transports call:

- `outbound(transport, correlationId, attemptId, half, localOwner, scope)`: the sender's trace
  header plus its staged symbolic values. The header is `1|span|epoch|kind|role|id|requestKey|
  requestApi` (`RuntimeTraceContext#header`); a send with no source or request flow goes without
  one and is named as a `MESSAGE_CONTEXT_REFUSED` DIAGNOSTIC row.
- `inbound(trace, symbolic, ...)`: ends the exchange the thread served and installs this one until
  the next message or `endInbound`; `keepSymbolic` keeps a multi-message exchange's values.
- `setAside` / `restore`: a serving thread that runs an exchange of its own as a client.
- `beginTick` / `vacant` / `endTick`: a daemon turn as a root; a vacant turn is one the recording
  never made, which a replay held and let go only because the run could go no further.

The Hadoop adapter is `src/shim/java/org/apache/hadoop/ipc/CausynthMessagePropagation`, shipped
with GraphChecker: transports `HADOOP_IPC` (IPC correlation) and `HDFS_SASL` (a handshake of
several messages on one thread, possibly opened by a thread serving a request). The HDFS trees call
it from IPC `Client`/`Server` and the SASL data-transfer classes; the Solr trees call
`MessageDoors` directly (HTTP headers through `CausynthHttp`, ZooKeeper through `SolrZkClient`).

### 7.2 Store doors

For a store the nodes share (ZooKeeper in a one-JVM cluster):

- `stored(transport, key, owner)`: a write of `path@version` is a SEND; its staged values are kept
  with the version.
- `notified(kind, callback)` + `fetched(transport, key, owner)`: inside a watch callback, the first
  read of a stored version installs the writer's context, with `via` = the watcher kind (and
  `.<n>` from a node's second delivery of that version on). Such receipts are unawaited: the work
  they anchor takes no place in the schedule. A read outside a callback is data, not a cause.
- `consumed(transport, key)`: a queue item's staged values arrive with it; the consumer keeps its
  own context.

### 7.3 Typed faults

The DOOR rows and the woven markers are SYMBOL-SCOPE.md §4.2. A marker's branch is a decision of
the occurrence that runs the door; `explore/ClosurePlanner#controlProducer` adds the sender and the
receiver of the message a demanded occurrence served (found through its `Anchor`,
`explore/Corpus#senderOf`, `#receiverOf`) as control producers, so their door faults are proposed
as flips.

### 7.4 Captures bound to exchanges

PLAN binds each wire capture of an activation to the exchange it ran in
(`RuntimeRegionPlanner#bindObservedCommunicationCaptures`): an OUT capture to the next SEND on its
lane, an IN capture to the latest RECEIVE, rewound to that exchange's first frame.

## 8. The schedule

`contract/ScheduleEvent` = (seq, kind, context, site, k, occurrence, endpoint). Kinds: `START`,
`CLAIM`, `SEND` (with the producer endpoint), `RECV`, `WAKE` (a timed wait's timeout; a tick's
begin), `END` (a tick's end), `INTERRUPT`. `context` = `<node>|<ctx render>[|<start frames>]`
(`ScheduleLog#contextOf`, `Identity#handoffs`); `k` counts events per (kind, context, site). A
`Lost` context, and a context anchored by an unawaited receipt, make no event. `mark` rows state
where each occurrence opened (the cut of a prefix focusing it); `{mark: WITNESS, at}` states the run
was cut at its witness.

`runtime/ScheduleLog` records in both passes into `schedule.jsonl`. In a replay it also holds the
order:

- the order is the source session's prefix (`CAUSYNTH_SCHEDULE_PREFIX` / `causynth.schedule.prefix`)
  then its rest (`schedule_suffix.jsonl`), cut by `explore/SchedulePrefix` at the task's target;
- an event takes the earliest open or given-up slot of its key; with none it runs free. A slot
  before the cut, or a `WAKE` slot anywhere, is held until every earlier slot is settled;
  `INTERRUPT` is never held;
- while the prefix stands, a `WAKE` with no slot is held too (`ScheduleLog#waitsAtLocked`). One the
  recording never made waits at the cut. One past its recorded count (a loop polling longer than
  recorded) waits until its context's next slot is due, then polls once per move of the order
  (a settled slot) since its previous `WAKE`; the slot its last recorded `WAKE` took counts, so
  the first poll past the count goes at once. A loop that reads a CLOCK root goes as soon as its
  slot is due: `runtime/ClockLoops` finds, on the waiting thread's stack, a method in which the
  scope map declares a CLOCK root (by method, so a clock read in a callee that returned before the
  wait is missed). The watchdog lets held waits go when the run idles; a released timed wait still
  waits out its own deadline. Past the cut a `WAKE` with no slot runs free, except in an order whose
  run was cut at its witness: that run's log states it (a `{mark: WITNESS, at}` row,
  `ScheduleLog#witnessed`, handed on in the rest by `SchedulePrefix#write`), it made nothing it does
  not list before the witness, so its order ends there and a `WAKE` with no slot waits at the
  order's end, not its cut, until every non-`WAKE` slot is settled (`ScheduleLog#line`; CONFIRM's
  unheld order included). Only a `WAKE` comes unbidden (a timer); any other event the order lacks
  follows a cause the order holds, and runs free;
- settling: a closed occurrence's untaken slots are dead; a turn's `END` gives up what the turn did
  not do; a waiter gives up what its own occurrence did not make before its slot; the watchdog
  acts after `causynth.schedule.timeout.ms` (default 15 s) with waiters, no slot settled and no
  workload thread computing, or after eight timeouts (`CEILING`) whatever they do. Every
  non-waiting thread counts except the engine's own (`causynth-*`: the result publication, the
  trace parse), since which thread owes a slot cannot be seen between two of its events
  (`ScheduleLog#computingLocked`). The watchdog first lets the waits held without a slot go; a
  grace (`LET_GO_GRACE_MS`, 2 s) later it gives up every open slot before the earliest waiter
  that waits for a slot. A poll held past its count stands at a due slot and waits for no slot's
  event, so it bounds no give-up; when only such polls wait, they are let go again, a grace
  apart. A let-go does not restart the stall's clock: a wait for a slot is held at most
  `CEILING` timeouts and a grace, and an event that never comes, with nothing computing, costs a
  timeout and a grace. After two give-ups past the cut the rest is released. Each let-go and
  give-up is a `SCHEDULE_DIVERGED` DIAGNOSTIC row;
- an obligation's replay is held to the schedule of the session whose path it flips, cut at its
  target occurrences (`explore/ObligationSolverMain`, `SchedulePrefix#write`), and inherits that
  session's world (its flips and planted values); flips are cut only from ADMITTED sessions
  (`explore/ObligationFactory`). CONFIRM writes the selected session's schedule unheld
  (`explore/ConfirmMain`, `SchedulePrefix#write` with `held` false): every event is rest, so only
  a `WAKE` still waits for what it followed, and the model's order is held by the `ORDER` rows of
  its expected edges (`runtime/Confirmation`, PIPELINE.md §10);
- `runtime/TimedWaits` replaces every timed wait in both passes; under a held `WAKE` slot the wait
  runs on virtual time (it ends at a real signal or when its slot is due), and a woven notify marks
  the longest-standing wait.

## 9. Selectors

A case names its target occurrence (`declared_target_occurrence`) as a selector
(`contract/Selector`), `<node>#epoch<N>/region/REGION.x[@<src>#epoch<N>/<api>]#k`, or as `first`,
the first observed occurrence of the declared target site in the recording (an ad-hoc sweep's default,
`plan/RuntimeWorkflowDiscovery.FIRST`). `plan/SelectorResolution#resolve` takes the k-th seed
activation a selector matches (region, and the anchor's api when given); an already-resolved
address passes through. No match yields a degraded address, reported downstream as
`DECLARATION_MISSING`.

## 10. Pass equality

The address is one function of one input set in both passes. The hooks that push a frame or count
an event (`startWork`, `claimStart`, `enterMethodFrame`, `exitMethodFrame`, `throwMethodFrame`) are
in both hook catalogs (`CausynthPipeline.HookCatalog#shared`); every site string is stabilized once
by `contract/JvmNames#stable` (reflection accessors and lambda proxies lose their JVM-minted
counters; a desugared lambda class is named by content in every weave, `LambdaClassNames`);
randomness is seeded by endpoint (SYMBOL-SCOPE.md §4.5).

## 11. Current limits

- The anchor is found through JVM-global tables (`Interactions`, `MessageDoors` stored versions);
  the header carries no endpoint, so a context crosses only between nodes of one JVM.
- `Interactions` evicts past 8192 entries; a receipt whose sender was evicted or never filed gets
  no anchor, and its work takes a `Root` or `Lost` context instead, named by a `LINEAGE_LOST` gap
  on the receiving occurrence with the eviction count (`RuntimeTraceContext#unanchored`).
- A different number of calls at one site on the index path moves the index; root `k` counts
  arrival order across threads of one (node, role, api); a pre-window turn is `Lost` and outside
  the schedule.
- Contexts and anchors exist only where a transport calls the doors. In the HDFS trees a
  DataTransfer operation is a tick root, not anchored to its sender; Solr's Overseer queue turns
  keep their own context; ZooKeeper watch work is outside the schedule.
- Threads started inside unscanned libraries have no start frame and inherit their creator's
  scope; pools other than the three in `PoolWorkers` are not recognized; timed waits outside the
  `WorkStartSites` list (`CountDownLatch.await(t)`, `Future.get(t)`, `Thread.join(t)`, ...) run on
  the wall clock.
- An unreadable schedule prefix lets the replay run free, stated on stderr only; a malformed
  timeout takes the default.
- Only a restart the workload reports through `restartSource` starts a new epoch.
