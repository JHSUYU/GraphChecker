# Identity: occurrences, contexts, doors, schedule

A causal graph node is one region occurrence `(r, c, i)`: the static region `r`, the causal context
`c` that started it, and the execution index `i` locating it in its component's control structure.
Recording and every replay compute it with the same function over the same woven hooks, so a node
of one run is the same node in another iff the ids are equal, the declared occurrence alone also by
its question (§9). Java paths below are under
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

**Unnamed work** (`Identity#occurrence`): work started where no hop named its starter (§3) opens
no occurrence while no hop names it either (its lineage is empty, `Lineage#named`: one test for
both); its region entries push a marker as a fold does, and its events are its role's. Such
siblings differ by nothing an address names: a DataNode's connection threads, which its acceptor
starts under no root, each enter the SASL server's regions before their first message, and would
share one address. Once the message's hop stands, the regions they enter open under it. Neither
pass records an activation for an entry that opened none (the trace states `regionFolded`; an
unnamed one has no owner). Never silent: each region a node's unnamed work entered is a
`LINEAGE_LOST` DIAGNOSTIC row (`RowRuntime#unnamedEntry`, in the recording's trace or the
session), the session manifest counts every entry (`unnamedEntries`), and a closure that reaches
such role work names the roots and decisions it left unrecorded (`ClosurePlanner#unrecorded`).

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
- **Start frames.** `Identity#startWork` files, per `Thread.start` or submission, the starter's
  index from its scope base followed by a frame (site, k-th start at that site) with the carrier;
  the started work claims them at its first identity event or at its functional method's entry
  (`#claimStart`). A task claimed on a pool's thread stands on all of them; a started thread
  already stands on its creator's frames and adds the start frame alone. So siblings started from
  one site differ by that frame's `k` or, started in two calls of the method holding the site, by
  the frames above it. Claimed starts nest; a pool thread drops a finished task's start levels
  before claiming the next. A start made where no hop names the starter (its lineage is
  empty) files no frame, captures no scope and writes no event -- its k would count arrivals,
  which nothing schedules -- but an unnamed start: the work that claims it is unnamed (§1), a
  started thread for its life, a task claimed on a pool's thread until the next claim on that
  thread or until a level below its claim exits.
- **Scope base** (`Identity#scopeStart`, `Hop`): an occurrence's index starts at its context's
  origin: the inbound scope for `ANCHOR` (which pooled handler serves a request is scheduling, not
  identity), the scope start for `SCOPE_ROOT` (a request, a carried scope, a wake turn), the claimed
  start frame for `STARTED_ROOT` (a daemon tick). A claimed start opens no scope
  (`RuntimeTraceContext#claimCarried`): a task's index runs from the claiming thread's base (a pool
  worker's own) through its start frame and holds none of the starter's frames, so two starts from
  one site in two calls of the method holding it can share an address.
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
unpaired. The `WIRE_FLOW` header does not carry the producer endpoint; a codec hole's envelope does,
and its attach is paired by `ENVELOPE` (§7.5).

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

`runtime/Attribution#resolve`, four rules in order: the innermost explicit scope on the thread
(a request, a registered inbound owner, a tick owner); else the innermost frame whose receiver is a
registered object, the receiver of the thread's last work entry (`Identity#claimStart`) counting
as its outermost; else, on a thread that claimed no start, the explicit scope its creator stood in
when it constructed it (`RuntimeTraceContext#inheritedSource`); else the node of whatever started
this work (followed through starters, at most 32 deep). All four failing is `null`, never a guess:
the activation is then attributed to `workload/unregistered`
(`RuntimeTraceContext#activationSource`), so every activation has an address. An activation under
a `Lost` context is a `LINEAGE_LOST` DIAGNOSTIC row (`runtime/RowRuntime#beginActivation`).

The system's test adapter registers nodes through `MessageDoors.registerNode` (anchor plus aliases:
the objects the node runs its work through), `registerSource`, `registerSourceAlias` and
`restartSource` (HDFS `CausynthCluster`, Solr `CausynthSolrCluster`, ZooKeeper `CausynthZkCluster`,
in the trees). Work on no registered node is attributed to `workload/unregistered`
(`RuntimeRegionPlanner.UNREGISTERED_SOURCE`).

PLAN refuses what the address cannot tell apart: activations of one region sharing one address are
`OCCURRENCE_ADDRESS_SHARED` (BLOCKING when the published closure retains that occurrence, else
DIAGNOSTIC, `causynth/RuntimeSelectedRegionFinalizer#stateSharedAddressClasses`), and a plan row whose causal anchor or source names
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

A start made under a hop (§3) captures the starter's scope with the carrier
(`RuntimeTraceContext#captureAsync`) and writes a `START` event; the claim restores it
(`RuntimeTraceContext#claimCarried`) and writes a `CLAIM` event. A start no hop names captures
nothing and writes no event; its work is unnamed (§1). A pool's own worker thread
inherits no scope (`runtime/PoolWorkers`: `ThreadPoolExecutor.addWorker`,
`ForkJoinPool.createWorker`, Jetty `QueuedThreadPool.startThread`); each task carries its own.

A new thread inherits its creator's lineage, execution index and trace scope through the engine's
inheritable thread-locals (`runtime/InheritedState`: `Lineage`, `Identity`,
`RuntimeTraceContext`). `Thread.init` computes them on the creator, inside whatever region it
stands in, and no weave brackets a call the JDK makes, so `InheritedState#childValue` pauses the
VM's propagation itself (`ConcolicVmBroker#pauseEngineWork`), as every woven hook call is paused:
the child inherits its identity, and the creator's objects get no shadow. Unpaused, the index's
list of the creator's frame receivers named each one by a container relation, so every later read
of their fields was symbolic: in hdfs-17960 a planned checkpoint handler's `Thread.init` read its
own `contextClassLoader` symbolically, and the image savers' `core-default.xml` parse was tracked
row by row.

The lineage scope (`plan/LineageScan`, run by `run_engine.sh campaign_lineage_classes` over
`causynth_lineage_roots`) weaves the start, claim and timed-wait hooks into every class of the
system's own class roots that starts, hands off, runs or waits, whether or not the case analyses
it.

## 7. Doors

### 7.1 Message doors

`runtime/MessageDoors` is the transport-neutral API every system's transports call:

- `outbound(transport, correlationId, attemptId, half, localOwner, scope[, payload])`: the
  sender's trace header plus its symbolic header. The trace header is `1|span|epoch|kind|role|id|
  requestKey|requestApi` (`RuntimeTraceContext#header`); a send with no source or request flow goes
  without one and is named as a `MESSAGE_CONTEXT_REFUSED` DIAGNOSTIC row. The symbolic header holds
  one space-separated segment per scheme: `CSE5` (the `WIRE_FLOW` values the thread staged) and
  `CSE6` (the codec holes of §7.5: the payload the door holds, walked with its transport's codec,
  and what the thread's open bracket of this transport staged).
- `beginExchange(transport)` / `endExchange(token)`: a bracket on the thread (a declared `EXCHANGE`
  method, woven; the SASL handshake, `beginSasl`/`endSasl` in the shim) whose EXCHANGE-bound
  encodes the next outbound message of that transport carries.
- `inbound(trace, symbolic, ...)`: ends the exchange the thread served and installs this one until
  the next message or `endInbound`, with the codec holes its envelope carried for the decodes the
  thread runs; `keepSymbolic` keeps a multi-message exchange's values of both schemes.
- `setAside` / `restore`: a serving thread that runs an exchange of its own as a client.
- `beginTick` / `vacant` / `endTick`: a daemon turn as a root; a vacant turn is one the recording
  never made, which a replay held and let go only because the run could go no further.

The Hadoop adapter is `src/shim/java/org/apache/hadoop/ipc/CausynthMessagePropagation`, shipped
with GraphChecker: transports `HADOOP_IPC` (IPC correlation) and `HDFS_SASL` (a handshake of
several messages on one thread, possibly opened by a thread serving a request). The HDFS trees call
it from IPC `Client`/`Server` and the SASL data-transfer classes; the Solr trees call
`MessageDoors` directly (HTTP headers through `CausynthHttp`, ZooKeeper through `SolrZkClient`), and
so does the ZooKeeper tree (`CausynthZk`: transport `ZOOKEEPER`, one `REQUEST` message per client
request, sent where `ClientCnxn` queues it, its header beside the bytes under the session and xid
they carry, served by the server's `PrepRequestProcessor` and `FinalRequestProcessor` stages).

### 7.2 Store doors

For a store the nodes share (ZooKeeper in a one-JVM cluster):

- `stored(transport, key, owner[, data])`: a write of `path@version` is a SEND; its staged values
  are kept with the version, and so are the codec holes an encode bound to `data` (§7.5).
- `notified(kind, callback)` + `fetched(transport, key, owner)`: inside a watch callback, the first
  read of a stored version installs the writer's context, with `via` = the watcher kind (and
  `.<n>` from a node's second delivery of that version on; how many deliveries a run takes is the
  store's timing, so CONFIRM names every delivery of one version alike,
  `CausalContext.Anchor#anyDelivery`). Such receipts are unawaited: the work
  they anchor takes no place in the schedule. A read outside a callback is data, not a cause.
  `fetched(transport, key, owner, data)` binds `data` to the version's codec holes on every read,
  inside a callback or not: a value is data, a notification a cause.
- `consumed(transport, key)`: a queue item's staged values arrive with it; the consumer keeps its
  own context.
- `storing(transport, location)` ... `storeEnded(transport, token)`: a write in flight at one
  location (a sequential create's: the prefix the store completes). The store applies a write,
  and notifies the version's watchers, before the write's call returns, so another thread can
  read the version before its writer files it (SOLR-18413 F2: node1's state watchers read the
  routing rule's version while the Overseer's turn was still in `stored`, and their work opened
  no occurrence). `stored` is in flight at its key's location until it has filed, and files the
  version last, after its codec holes; an adapter opens the bracket before the store's call and
  closes it in a `finally` after `stored`, so the store's own latency is inside it too. A read
  that takes what its write carried (`consumed`, `fetched` in a callback or with its bytes) and
  finds the version unfiled waits for the writes other threads had in flight at the version's
  location when it read -- that location, or a sequential prefix of it, never a parent --
  (`MessageDoors#filed`): the one that made the version files it before its bracket ends. A
  version no such write files was made outside the window or carried nothing; its read names
  nothing and waits for nothing begun after it. The wait is bounded (`FILED_WAIT_MS`, 2 s: the
  writes file within milliseconds): a writer held behind the reader -- before a replay's cut a
  writer may be held at its SEND while a reader waits for it -- costs the bound, and the read
  then names nothing and a DIAGNOSTIC `LINEAGE_LOST` row names the version and the writes still
  in flight. Writes at other locations, of the same transport or not, order nothing.

### 7.3 Typed faults

The library catalog's doors and the woven markers are SYMBOL-SCOPE.md §4.2. A marker's branch is a decision of
the occurrence that runs the door; `explore/ClosurePlanner#controlProducer` adds the sender and the
receiver of the message a demanded occurrence served (found through its `Anchor`,
`explore/Corpus#senderOf`, `#receiverOf`) as control producers, so their door faults are proposed
as flips. PLAN plans the door occurrences that read a fault marker on the same relation, over the
recording's schedule (`causynth/RecordedMessages#doorsOf`, SYMBOL-SCOPE.md §4.4), so the faults EXPLORE
proposes are minted.

### 7.4 Captures bound to exchanges

PLAN binds each wire capture of an activation to the exchange it ran in
(`RuntimeRegionPlanner#bindObservedCommunicationCaptures`): an OUT capture to the next SEND on its
lane, an IN capture to the latest RECEIVE, rewound to that exchange's first frame.

### 7.5 Codec holes

A value a serialization format carries crosses as holes (WIRE-CODEC; declarations in
[CONTRACT-SPEC.md §6](CONTRACT-SPEC.md)). `causynth/CodecWeave` hooks each declared encoder's
returns, each decoder's returns (or entry, for a graph argument) and each `call` pattern's call
sites, entering its codec on entry and leaving it on every exit so a declared method inside another
of the same codec is transparent; and brackets each declared `EXCHANGE` method.

- **Encode** (`runtime/CodecRuntime#encoded`): `runtime/CodecWalker` walks the graph through the
  codec's views (a TREE's maps, ordered collections, arrays and `CODEC_VIEW` objects; a PROTOBUF
  message's `*_` fields; a LEAF graph whole) to every leaf whose port (`codecPortId(space, key)`) is
  demanded (`runtime/DemandedPorts`: the `CODEC_PORT` rows the file `causynth.codec.ports` names).
  `runtime/CodecExport` reads each leaf's expression from the VM (`exportLeaf`, by its slot) and
  cuts it into a template of literals and holes; each hole's producer endpoint is minted now.
- **Binding** (`runtime/CodecMessages`), never the thread: an encode bound to its encoded object
  waits for the store door that writes that object; an EXCHANGE-bound encode stages into the
  innermost open bracket; a door's own payload is walked at the door. An encode no message carries
  is counted (`CODEC_MISMATCH` `UNSENT`, one row per codec at the run's close).
- **Envelope** (`runtime/CodecEnvelope`, `CSE6`): per hole its codec, encode ordinal, key path,
  hole index, the leaf's template, the producer endpoint, the export event and the recorded texts;
  at most 256 per message, and the whole symbolic header (`CSE5` first) within its transport's
  `envelopeBytes` (4096 unless declared), each cut named `BOUND_INSUFFICIENT`. A header segment of
  no scheme is refused by name (`MESSAGE_CONTEXT_REFUSED`). Each hole a message carries publishes
  its `ExportRow` then, keyed by the message (`<transport> <path>@<version>` or the correlation id).
- **Decode** (`CodecRuntime#decoded`): the message bound to the encoded argument (a stored
  version's read), else the thread's inbound exchange's, else none; the first encode of the codec
  whose paths all resolve in the graph. `HandoffMint#mintHoles` reads each leaf against its
  template (`CodecExport.Reading`): only the value the producer recorded is minted, as the template
  or, when the producer's template was one whole-leaf hole, as one hole of the leaf's own sort;
  anything else is a `CODEC_MISMATCH` and the leaf stays concrete, paired with nothing (local data
  of the same message type meets an exchange's entries this way; WIRE-CODEC designer decision 14,
  over §4.3's one STR hole). It plants a wave's answer, stores a fresh copy of a
  String leaf wherever its holder can hold one, and mints the holes (`mintLeaf`: a String's template
  on its own object, so any read that returns it hands a parse or split the template itself; a
  primitive or a box at its slot; the VM never puts an expression on a JVM-wide object and never
  replaces one: a refusal of the leaf object (`landsOn: OBJECT`, `SHARED` or `SHADOWED`) is
  re-homed by a fresh equal object stored through its holder, or named `LEAF_SHARED` /
  `LEAF_SHADOWED` when the holder cannot take one; a slot's refusal stands, named by its status)
  and publishes one `AttachRow` per hole, paired by `ENVELOPE`. Entries are never consumed: N readers of one version, and one decode twice, each mint
  their own.
- **Endpoints**: a hole's endpoint site is the port; its event frame is
  `port@<storeKey><keyPath>#<hole>` (`Identity#endpointAt` with a frame site; the store key is
  empty for an exchange and at the encode), with `/`, `@` and `%` escaped, so two queue items one
  occurrence decodes stay apart. The consumer is the innermost live region, else the occurrence
  running here (an ambient mint, which records no path). A hole's symbol is named by
  `(port, consumer occurrence, k, keyPath#hole)`, as a `WIRE_FLOW` attach's is.

## 8. The schedule

`contract/ScheduleEvent` = (seq, kind, context, site, k, occurrence, endpoint). Kinds: `START`,
`CLAIM`, `SEND` (with the producer endpoint), `RECV`, `WAKE` (a timed wait's timeout; a tick's
begin), `END` (a tick's end), `INTERRUPT`. `context` = `<node>|<ctx render>[|<start frames>]`
(the claimed starts' levels, each start's own frame after the starter's frames it was filed with)
(`ScheduleLog#contextOf`, `Identity#handoffs`); `k` counts events per (kind, context, site). A
`Lost` context, and a context anchored by an unawaited receipt, make no event. `mark` rows state
where each occurrence opened (the cut of a prefix focusing it); `{mark: WITNESS, at}` states the run
was cut at its witness.

`runtime/ScheduleLog` records in both passes into `schedule.jsonl`. In a replay it also holds the
order:

- the order is the source session's prefix (`CAUSYNTH_SCHEDULE_PREFIX` / `causynth.schedule.prefix`)
  then its rest (`schedule_suffix.jsonl`), cut by `explore/SchedulePrefix` at the task's target;
- an event takes the earliest open or given-up slot of its key that its own occurrence made, else
  the earliest of its key (`ScheduleLog#slotOf`: two concurrent RPCs under one context share a key
  and must not swap slots); with none it runs free. A slot
  before the cut, or a `WAKE` slot anywhere, is held until every earlier slot is settled;
  `INTERRUPT` is never held;
- while the prefix stands, a `WAKE` with no slot is held too (`ScheduleLog#waitsAtLocked`). One the
  recording never made waits at the cut. One past its recorded count (a loop polling longer than
  recorded) waits until its context's next slot is due, then polls once per move of the order
  (a settled slot) since its previous `WAKE`; the slot its last recorded `WAKE` took counts, so
  the first poll past the count goes at once. A loop that reads a CLOCK root goes as soon as its
  slot is due: `runtime/ClockLoops` finds, on the waiting thread's stack, a method in which the
  scope map declares a CLOCK root (by method, so a clock read in a callee that returned before the
  wait is missed; the methods are installed from the rows the session reads when it opens,
  `GuardedStoreSites#install`, never at a wait, where reading the map held a thread's first wait
  seconds mid-run and timed out an IPC caller's hand-off to its sender). The watchdog lets held waits go when the order stalls; a released timed wait
  still waits out its own deadline. Past the cut a `WAKE` with no slot runs free, except in an
  order whose run was cut at its witness: that run's log states it (a `{mark: WITNESS, at}` row,
  `ScheduleLog#witnessed`, handed on in the rest by `SchedulePrefix#write`), it made nothing it does
  not list before the witness, so its order ends there and a `WAKE` with no slot waits at the
  order's end, not its cut, until every non-`WAKE` slot is settled (`ScheduleLog#line`; CONFIRM's
  unheld order included). Only a `WAKE` comes unbidden (a timer); any other event the order lacks
  follows a cause the order holds, and runs free;
- settling: a closed occurrence's untaken slots are dead; a turn's `END` gives up what the turn did
  not do; a waiter gives up what its own occurrence did not make before its slot. The watchdog
  watches the order's frontier (`ScheduleLog#firstBlocking`: the first open slot that is no
  `WAKE`), which every wait for a slot or for the line waits on. It acts once the frontier has
  stood `causynth.schedule.timeout.ms` (default 15 s) with no thread computing toward it, or eight
  timeouts (`CEILING`) whatever threads do, both counted from the frontier's last move or its
  earliest current waiter's arrival, whichever is later (`ScheduleLog#stallSinceLocked`): the
  frontier owes nothing to a wait that has not begun. A slot taken past the frontier (past the cut
  a non-`WAKE` slot is taken at once) or an event run free moves no wait for a slot or the line,
  so it does not restart the stall (hdfs-17899-bug2 w4d1 CONFIRM: the test thread's polls took
  their later slots, then ran free, for the whole of its 30 s wait while a BPServiceActor, held at
  the order's end in a wait the recording never timed out, owed the frontier, its turn's `END`); a
  poll past its recorded count goes on any move, but it waits for no slot's event. The CPU is
  looked at once a second (`ScheduleLog#lookLocked`), the first look of a stall measuring from its
  start. Something computes toward the frontier when its owner was seen at work: an event in the
  frontier's own context or occurrence (where `#slotOf` and `#passedLocked` place a thread's own
  events) since the last look, whatever CPU share the owner gets (the VM's arena mutex, a
  collection, a busy host), except a poll past its recorded count that went only because the order
  moved or it was let go (a loop reading a CLOCK root, or a `WAKE` taking its slot, is at work).
  Otherwise which thread owes the frontier cannot be seen between two of its events, so any thread
  may, except one waiting for a turn, the engine's own (`causynth-*`: the result publication, the
  trace parse), and one seen at an event away from the frontier since the last look (run free or
  into a slot past it, in neither its context nor its occurrence; a thread the watchdog let go
  since the frontier moved is never away): it runs on elsewhere (`ScheduleLog#ELSEWHERE`). An
  unseen owner is one thread, so one such thread's CPU plus the collectors' time over half the
  look's span defers the give-up, not a sum: the traffic a free-running loop drives through threads
  that make no event (an IPC reader, a connection's receiver) is no one computing. The watchdog
  first lets the waits held without a slot go; a grace (`LET_GO_GRACE_MS`, 2 s) later it gives up
  every open slot before the earliest waiter that waits for a slot. That is one let-go per
  frontier: a slot taken past it earns the held waits no second one, which would hold the give-up
  off for as long as anything ran elsewhere. A poll held past its count stands at a due slot and
  waits for no slot's event, so it bounds no give-up; when only such polls wait, they are let go
  again, a grace apart. A let-go does not restart the stall's clock for the waits that remain: a
  wait for a slot is held at most `CEILING` timeouts and a grace, and an event that never comes,
  with nothing computing toward it, costs a timeout and a grace. After two give-ups past the cut
  the rest is released. Each let-go and give-up is a `SCHEDULE_DIVERGED` DIAGNOSTIC row;
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
`plan/RuntimeWorkflowDiscovery.FIRST`; a case stating none is refused at PLAN). The recording's aggregation
resolves it once, against the target occurrences it observed in recorded order
(`RuntimeWorkflowDiscovery#declaredOccurrence`: the k-th a selector matches, by `SelectorResolution`'s
rule), marks that occurrence's plan row, and plans only the question `(r,c)` around it: the target
occurrences of its region and node whose context has its shape (`contract/ContextShape#sameQuestion`,
the rule `explore/Branches` stops replays by), at any index (SYMBOL-SCOPE.md §4.4). Every stage after
PLAN reads the resolved address. `plan/SelectorResolution#resolve` takes the k-th seed activation a
selector matches (region, and the anchor's api when given); an already-resolved address passes
through. No match yields a degraded address, reported downstream as `DECLARATION_MISSING`.

**A replay's answer.** One woven entry per root hook group (`plan/ExecutionTask#rootHookGroup`:
region, root method, a loop-body root's loop) offers each invocation to every task of its group, and
a replay admits a planned task by its whole address, id against id
(`runtime/ConcolicTaskPlan#select`), with one exception: the declared occurrence is also answered by
its question. PLAN states its context's shape over the recording's senders on its row
(`questionShape`, `causynth/RuntimeSelectedRegionFinalizer`, `RecordedMessages#shape`); an
activation of its region on its node, in a context no task of that root plans an occurrence of the
region in (`ConcolicTaskPlan#occupies`: not its address, and not another invocation under the same
anchor, which is the planned occurrence's; hdfs-11741 K2: the second `handle()` call of one balancer
handshake, under the anchor of that handshake's planned first call, answered the declared second
handshake, which then ran unplanned), at an address the recording did not open itself (PLAN states
the ids of every other occurrence the recording opened in the region on the node, `questionRecorded`,
`RuntimeTask#recorded`: an activation at one of them is that occurrence, whatever it serves this run;
accept-SB2: the Solr Overseer's first task, the collection's CREATE, took the address of the declared
second, the REINDEX, whose own entry then ran unplanned), in an entry that
opened its own occurrence, answers it when its own context, shaped over this run's senders
(`runtime/ScheduleLog#shape`: each producer endpoint's SEND stance), has that shape hop for hop and
reaches a root (`ContextShape#answers`: no unnamed hop, no `Lost`). The occurrence it opened then
takes the declared address (`Identity#answer`): its rows, endpoints, decision ordinals, schedule
mark and close state it, so every later stage reads the declared address as before, and a
DIAGNOSTIC `ADDRESS_UNSTABLE` row names the address the run computed (`RowRuntime#answered`). Which
turn of a daemon carries another node's asynchronous work is that node's timing, which no schedule
holds: in sweep `a40h` a NameNode command (block recovery queued by the lease monitor, replication
after a volume removal) rode a DataNode heartbeat other than the recorded one (#4 for #3, #8 for #6),
so every anchor below it differed in the root's k alone and the target was never admitted; two
recordings of one workload differ the same way.

## 10. Pass equality

The address is one function of one input set in both passes. The hooks that push a frame or count
an event (`startWork`, `claimStart`, `enterMethodFrame`, `exitMethodFrame`, `throwMethodFrame`) are
in both hook catalogs (`CausynthPipeline.HookCatalog#shared`); every site string is stabilized once
by `contract/JvmNames#stable` (reflection accessors and lambda proxies lose their JVM-minted
counters; a desugared lambda class is named by content in every weave, `LambdaClassNames`);
randomness is seeded by endpoint (SYMBOL-SCOPE.md §4.5).

## 11. Current limits

- The anchor is found through JVM-global tables (`Interactions`, `MessageDoors` stored versions);
  the trace header carries no endpoint, so a context crosses only between nodes of one JVM (a codec
  hole's producer travels in its envelope).
- `Interactions` evicts past 8192 entries; a receipt whose sender was evicted or never filed gets
  no anchor, and its work takes a `Root` or `Lost` context instead, named by a `LINEAGE_LOST` gap
  on the receiving occurrence with the eviction count (`RuntimeTraceContext#unanchored`).
- A different number of calls at one site on the index path moves the index; root `k` counts
  arrival order across threads of one (node, role, api); a pre-window turn is `Lost` and outside
  the schedule.
- Only the declared occurrence is answered by its question (§9), and only at a root entry, not a
  loop body. Every other task still needs its whole address, so the chain a replay took to the
  declared occurrence instead of the recorded one has no planned rows, and that session sends no
  message under the declared anchor: EXPLORE finds no door of it there
  (`explore/ClosurePlanner#controlProducer`).
- A codec decode on a thread no node is attributed to mints its holes under the unregistered
  address (the Solr Overseer reads its queue item before its tick opens, so the queue's holes are
  minted there, not in the tick).
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
