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
  epoch advances only when the workload or its cluster adapter calls `restartSource` (a restart, §5).
- **r**: a `REGION.<hash>` skeleton id (`causynth/SymbolicRegionPlanner`, a region rooted at an
  execution-context entry: `MAIN_ENTRY`, `THREAD_ENTRY`, `TASK_ENTRY`, `COMMUNICATION_ENTRY`,
  `STATE_WRITER_ENTRY`, `FAILURE_TARGET_ENTRY`, `EXPLICIT_FAULT_ENTRY` where neither an execution
  context nor the target already roots the method that reads a fault marker), or `ROLE.<role>` for
  work under no region (`runtime/Identity#roleOccurrence`). A region whose closure holds the
  failure is the failure's exception context whatever roots it. One loop iteration is the activation
  (`LOOP_BODY_ROOT`, `causynth/StaticProgram#loopBodyRoot`) where three hold: the loop is a service
  loop of the region (it issues the call into the region's work; an indexed loop only where an
  iteration is one unit of demanded work), the recording saw it decide its continuation more than
  once in one activation, and an iteration's frame can open at that call
  (`causynth/CfgLoopControl#bodyEntry`: the call is a member of the loop the header dominates, and
  one outermost body unit a control edge enters holds it -- the frame opens on every control edge
  into that unit, so `if (a || b) work();` is one entry -- or none does and the frame opens at the
  header). SEED states the placeable calls on each retained-loop row (`bodyEntryCallUnits`) and the
  weave asks the same function, so the recording, PLAN and every replay agree; a call on a path
  leaving the loop runs once per call of the method (hdfs ad-hoc `INodesInPath.getExistingINodes`),
  and where no loop qualifies the region's root is the activation, never a fallback at run time. An
  iterated loop holding the call where no frame can open is a DIAGNOSTIC `ADMISSION_GAP`
  `LOOP_BODY_UNPLACEABLE:<loop>@u<unit>@<region>` in the plan.
- **c**, **i**: §2 and §3. Nothing else enters the id: no thread id, object address or run ordinal.

`runtime/Identity#occurrence` is the one computation, called at region entry in both passes;
offline stages read the address the recording stated (`runtime/RuntimeRegionPlanner#recordedNode`)
and never re-derive it.

**Fold rule** (`Identity#fold`): a declared region entered synchronously inside a running
occurrence opens none; its events belong to the running occurrence, and a marker region keeps the
region stack balanced. An occurrence opened with a `Lost` context folds what is entered while the
thread is still `Lost`; the hop that gives it a context names it (below). A thread boundary always
ends an occurrence: a child thread
inherits region depth but no occurrence. PLAN records the folded regions on their owner
(`RuntimeRegionPlanner#stampFoldedRegionEntries`).

**Unnamed work** (`Identity#occurrence`): work started where no hop named its starter (§3) opens
no occurrence while no hop names it either (its lineage is empty, `Lineage#named`: one test for
both); its region entries push a marker as a fold does, and its events are its role's. Such
siblings differ by nothing an address names: a DataNode's connection threads, which its acceptor
starts under no root, each enter the SASL server's regions before their first message, and would
share one address. Once the message's hop stands, the regions they enter open under it. A message
unnamed work sends files no producer endpoint (`Identity#messageSent`), as its start filed no frame
(§3): its index would count what sibling threads did, and two IPC handlers' responses would share one
anchor (round HG2). Its receipt is unanchored, a `LINEAGE_LOST` row (`RuntimeTraceContext#unanchored`),
and the work it opens stands on the receiver's own context.

**Naming rule** (`Identity#hopOpened`, the same rule at every hop, in both passes): a hop that gives
the thread a context of its own (`RuntimeTraceContext`'s openers: a request, a carried scope or
claim, a tick, a wake turn, an inbound message) names the region its work stands in when that
region's entry has no name -- unnamed work entered it, or it opened `Lost` (a turn begun before the
window). Of several such standing entries the outermost is named: what it entered before the hop is
its work, as the fold rule makes the enclosing occurrence the owner. The region opens an occurrence
under the hop (its index §3), what it enters meanwhile folds into it, and its decisions count from
1; it ends at the hop's end (`#hopClosed`) or its entry's exit, whichever comes first, and the entry
is what it was before. So a daemon whose service loop was entered once, before the window or under
no root, has one occurrence per turn: DataNodeDiskMetrics' detector, whose `max > 0` decision and
store of `slowDisksToExclude` are its `run()`'s, opens `REGION(run)/ctx:Root:WAKE/
DataNodeDiskMetrics$1.run#k` at each wake. The recording states it as an activation of its own: the
region root's call and every call standing above it write an entry row again under a new id, the
root's with the address, and their rows state those ids while it stands
(`CausynthTraceRecorder#regionNamed`); at the hop's end they close under it and state themselves
under the root's own chain again. A replay admits the task planned there, by its whole address, at
the hop (`ConcolicRegionRuntime#regionNamed`, `ConcolicTaskPlan#selectNamed`) and starts its VM
region mid-method: the VM's attach shadows every frame then standing with no expression
(`ShadowStack`'s constructor), so the region's work before the hop is concrete and stated by
nothing. Its activation ends with the occurrence, by a throw when its entry exits by one.

Neither pass records an activation for an entry that opened none (the trace states
`regionFolded`; an unnamed one has no owner). Never silent: each region a node's unnamed work entered is a
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
| `beginRequest` (the workload, `MessageDoors.beginRequest`/`beginWorkloadCall`) | role `CLIENT`, api = the request's name; a root where none stands, or always (`pushCallRoot`) for a workload call. It stands until its end, past the traced activation it began in (`RuntimeTraceContext#exitRoot`: the thread's request flow stays its, where an exchange received in the activation ends with it) |
| `beginTick` (`MessageDoors.beginTick`) | a root of the given role, whatever the thread stands in (`pushRoot`), once the exchange the thread served has ended (§7.1) |
| `beginWake` (at the return of a timed wait, `runtime/WakeScopes`) | a root of role `WAKE`, api = `Class.method` of the wait; only on a thread attributed to a node and only when every open scope is itself a turn (a request, a served message, a node startup are not: a wait inside them is a pause) |
| `enterInbound` (a received message) | role = the transport, api = the request's `<source>/<api>`; the anchor is `Interactions.sender(transport, correlation, half)`, rpcSite `<TRANSPORT>[.<VIA>]/<api>` |
| `enterCarriedScope`, `claimCarried` (queued or started work) | the carried lineage restored, plus a nested hop (`EXECUTOR_TASK` for a claimed start) |

`k` counts root hops only, per (window, node, role, api), in one JVM-wide counter
(`Lineage#push`). A turn begun before the window has `k = 0` (`Lineage#rootWindowIndex`), so its
context is `Lost`; a request begun before the window keeps its `k`. A turn (a tick, a wake turn) is
named once an identity reads its `k` (`Identity#here`: a schedule event, an occurrence, an endpoint,
a draw), or once work started or captured in it carries its frames (`Lineage#carried`: a thread
started there, a task captured there, which read the `k` whenever they run); the flow key, the WAKE
its begin computes and a held timed wait's WAKE are read `Lineage#quietly`, as the recording, which
holds nothing, computes no held wait's WAKE. One that ends unnamed gives its `k` back
(`Lineage#pop`, a compare-and-set, so only while no later turn of its counter took one). A loop
spinning through turns that do nothing (hdfs-adhoc-16: a DataNode actor whose heartbeats a test
disabled never waits; 0.89M turns recorded, 47k replayed) then moves no `k` of the turns that act.
The turn that takes a given-back `k` again collides with nothing: the turn that gave it back wrote
nothing under it and handed its frames to no work. The ks are equal in both passes where one thread
takes a counter's turns (a daemon's loop); turns of one counter on several threads may interleave
their gives-back differently.

## 3. The execution index `i`

`contract/Frame` = (callSite, k), rendered `callSite@k`; `contract/ExecutionIndex` = a list of
frames with hash `fold(h, f) = sha16(h + "/" + f.callSite + "@" + f.iteration)`.

- **Frames.** Every application-scope method opens a level at entry and closes it at every exit,
  in both passes (`Identity#enterFrame`, `#exitFrame`). A frame's `k` is the k-th event at that
  site in the enclosing level under the root hop that owns the count (`State#nextSiteEvent`, keyed
  by level, root-hop token and site): the one the occurrence running on the thread was opened or
  named under (`State#countingRoot`, `Region#root`), else the current root hop. It is not a
  loop-iteration count. An occurrence's address is its frame path within it and names no root hop
  opened inside it, so such a hop restarts none of its counts: in round HG5A's hdfs-adhoc-21 a
  DataNode actor's `run()` occurrence, entered in the startup window under the test's request,
  sent every turn's heartbeat at `offerService@0/sendHeartBeat@0`, one producer endpoint for three
  turns, and the NameNode served all three under one anchor at one address.
- **Start frames.** `Identity#startWork` files, per `Thread.start` or submission, the starter's
  index from its scope base followed by a frame (site, k-th start at that site) with the carrier,
  and what the work was submitted to: the submission's receiver, woven as the hook's third argument
  (`CausynthPipeline#fileStarts`; null for a static call), whose hand-off it records
  (`Identity#handsOff`: a `ThreadPoolExecutor` on a `SynchronousQueue`), so a claim states its kind
  (§10). Classes woven before that argument call a `startWork` that is gone: every tree is re-woven.
  That `k` counts starts at the site in the top level under the hop that gives the context -- the
  innermost hop carrying an anchor, else the root (`State#nextStartEvent`, `Lineage#contextToken`)
  -- not under the whole root hop: under a test's one request every poll and node start before it
  moved a shell command's thread's `k` (hdfs-adhoc-35: `@317` recorded, `@404` replayed). Two works
  cannot share an address by it: each carries the context of the hop its start was counted under.
  A start made with a request in hand hands that request off: its site is `<site>:<verb>` and its
  `k` counts per verb (`Identity#requestInHand`). The verb is per thread, set by every outbound to
  the message's verb (`""` where its door names none, and for a response), cleared by every inbound,
  and never inherited by a thread the holder starts; the Hadoop IPC caller sends its request, offers
  it to the connection's sender (the start), waits and receives the response, so a DataNode turn's
  heartbeat hand-off no longer takes its block report's `START` and `CLAIM` (hdfs-adhoc-15). A
  message door's fault clears it too, as a receipt does: the exchange ended, in failure
  (`Identity#doorFaulted`, one rule, called where a run decides a marker `true`: a replay's mint,
  `RootMint`, by the marker name its FAULT input states (SYMBOL-SCOPE.md §4.2), and a native
  reproduction's plant, `RecordingPlant#marker`). A demanded door's fault, a local file operation,
  ends no exchange (`LibraryCatalog#exchangeMarker`). Left in hand, a fault renamed every later start
  of its thread: in hdfs-17899-bug2 the test thread started the SPS daemon, after the key manager's
  `getBlockKeys` faulted at its IPC request door, as `Daemon.start()#u5:NamenodeProtocol.getBlockKeys`,
  an address no plan instrumented, so the key id's producer went unattested.
  The frames go with the carrier;
  the started work claims them at its first identity event or at its functional method's entry
  (`#claimStart`). A task claimed on a pool's thread stands on all of them; a started thread
  already stands on its creator's frames and adds the start frame alone. So siblings started from
  one site differ by that frame's `k` or, started in two calls of the method holding the site, by
  the frames above it. Claimed starts nest while their work runs: a work entry's claim ends when
  the entry returns (`#claimStart` / `#endClaim`, woven around the entry outside its level), with
  the scope it carried, and puts back what it replaced; left standing, an event loop's callbacks
  ran on its last task's frames and each send nested under the one before (HBA1: 3777 frames). Work
  its starter runs itself (an executor that runs a task on the calling thread) stands on the
  starter's frames already and opens the start frame alone (`Start#ranHere`). A queue item's claim
  lasts until the consumer takes its next item in the same work (`#claimItem`), and carries whoever
  put the item there, whichever node the consumer serves otherwise: Hadoop IPC's one
  `RpcRequestSender` per connection sends every in-JVM DataNode's calls (V22: refusing items of
  another node dropped their CLAIMs, the order stalled, and a daemon heartbeat took the key update).
  A start made where no hop names the starter (its lineage is
  empty) files no frame, captures no scope and writes no event -- its k would count arrivals,
  which nothing schedules -- but an unnamed start: the work that claims it is unnamed (§1), a
  started thread for its life, a task claimed on a pool's thread until it returns.
- **A received message's hand-off** (`system/hdfs` only; `system/solr` has no such door). A thread that hands a
  received message to a worker queue names the hand-off by the message (`MessageDoors#handingOff`,
  `Identity#handoffStarting`; from the Hadoop
  trees' IPC `Server#internalQueueCall` through the shim, `CausynthMessagePropagation#handingOff`, the
  call's correlation): every start it makes meanwhile is `<site>:<transport>.<sender endpoint>` --
  the endpoint the receipt's anchor names too -- standing on none of the thread's own frames, so its
  `k` counts that message alone and the handler's CLAIM follows it. Counted per thread, the IPC
  Reader's `internalQueueCall` was the k-th call of its connection: one call a replay did not make
  renamed every later call of that connection, each a stall (hdfs-adhoc-21, round TM13: 14 of 17). A
  message whose sender this run did not file names nothing; its hand-off is a plain start. The
  receiving side's twin of the request's level below.
- **A request's level.** A request starts at its RPC engine's invoke point, before the client's call
  (`MessageDoors#requestStarting`, from the Hadoop trees' `ProtobufRpcEngine2`/`ProtobufRpcEngine`
  `Invoker#invoke` through the shim, closed by `#requestEnded` in its `finally`). A RESPONSE its thread
  received is over (§7, the rule a startup and a turn follow), so the request stands in the thread's
  own context, not on that response's anchor; a REQUEST the thread serves stands, so a handler's nested
  call is its call's. It is in hand from there to its end (`Identity#requestInHand`; `#requestEnded`
  clears it, so a call that failed before its send names no later start) and opens a level of its own at
  its message site `<transport>#REQUEST:<verb>` (`State#requestFrame`), whatever of the client the
  case's scope frames: its `k` counts that site in the enclosing level under the ROOT hop that owns the
  count (`State#nextSiteEvent`, as frames are; a start counts per context hop, `#nextStartEvent`), so a
  request of another verb renames no later one, and the client's call inside it is plain. A retry
  (attempt `a`, the retry count a retry handler set with the call's id, `Client#causynthAttempt`) is
  its original's `k` at `<site>#retry<a>`; one whose original this level did not count (an
  asynchronous retry on `AsyncCallHandler`'s thread) is counted at that site. Round SL1-3
  hdfs-adhoc-52: every request the test made stood on the previous response's anchor and its
  `Client.call@k` counted all its RPCs, so one extra RPC renamed every later NameNode context (a 17 s
  give-up per recorded slot). Limits: a framed client translator (`*TranslatorPB`) is re-entered per
  retry, so a retry stands under the translator's next `k`; a retry handler's sleep, where woven, is a
  timed wait that may open a WAKE root; an application's own retry is a new call id, a new request of
  its verb.
- **Scope base** (`Identity#scopeStart`, `Hop`): an occurrence's index starts at its context's
  origin: the inbound scope for `ANCHOR` (which pooled handler serves a request is scheduling, not
  identity), the scope start for `SCOPE_ROOT` (a request, a carried scope, a wake turn), the claimed
  start frame for `STARTED_ROOT` (a daemon tick). A claimed start opens no scope
  (`RuntimeTraceContext#claimCarried`): a task's index runs from the claiming thread's base (a pool
  worker's own) through its start frame and holds none of the starter's frames, so two starts from
  one site in two calls of the method holding it can share an address.
- **Occurrence index** = frames from the scope base to the region entry (`#regionEnter`); for an
  occurrence a hop named (§1), the frames from the hop's scope base to where the hop opened, empty
  for a hop opened in the region's own method. Its events are indexed from its entry's base, as
  before the hop.
- **Window rule** (`runtime/RecordingWindow`): the workload opens the window
  (`MessageDoors.startRecording`) and may close it (`stopRecording`); every count restarts at the
  window, and a frame entered before it stands at `k = 0` in any address. A site its level reached
  before the window under a hop still open restarts at 1 (`Counters#reopened`): with m entries
  before the window, in-window entry j is `@(j + [m > 0])`, the m entries standing at 0, one perhaps
  still running (round SL1, hdfs-adhoc-39: the NameNode's blockReport handler serving a DataNode's
  report queued two storage reports through `runBlockOp`, the first before the window; restarted at
  0 both lambdas stood at `runBlockOp@0`, one address for two activations). Two passes agree where
  their m are equal, or 0 and 1 (the window opened before, or during, one call); they do not where m
  is 1 and 2, nor 0 and m >= 1 where the earlier entries are set-up noise that differs between the
  passes (the first in-window entry is then `@0` in one, `@1` in the other). Two entries before the
  window still share `@0`, reachable within one pass where a handler queues work once per storage
  without waiting (`NameNodeRpcServer#blockReceivedAndDeleted`): PLAN names that address
  OCCURRENCE_ADDRESS_SHARED (`RuntimeSelectedRegionFinalizer`, BLOCKING when the closure retains
  it), reported, never silent. An entry reads the window once, for its count and its level (a
  start: for its count and its filed frames), so an entry racing the opening keeps no set-up count
  inside the window. Neither the trace nor the
  schedule states anything before the window opens. The system's cluster adapter opens it once the
  cluster is up, or, for a case that declares `recording_window=startup` (an opt-in, owner-approved
  for bugs whose guard runs or whose fatal value is set while the cluster starts: a DataNode's
  handshake, a NameNode's format), before the cluster starts (`MessageDoors.startupWindow`, the JVM
  property `causynth.recording.window` every workload JVM of the run gets from
  `experiments/lib/execute.sh`); its nodes are then constructed and started inside the window, under
  the test's request (§5).
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
  `Endpoint#stateSite`; a location's INITIAL is `:INITIAL` at the access that started its log,
  `Endpoint#initialSite`, so it is no event of that access), or `<transport>#<half>` for a whole
  message, `<transport>#<half>:<verb>` where its door names the operation the message asks for
  (`Endpoint#messageSite`, `MessageDoors#outboundRequest`; no verb spells `/` or `@`). The HDFS IPC
  client door names `<protocol>.<method>` off its request (the shim's `outboundRequest`, Hadoop's
  own `RpcProtobufRequest#toString`), a constant of the call, so k counts the requests of one
  operation: a DataNode turn that sends a heartbeat before a block report, where the recorded turn
  sent the report alone, no longer gives the heartbeat the report's endpoint (hdfs-adhoc-15: the
  NameNode's handler under the report's anchor answered a heartbeat and never made the recorded
  enqueue). A door naming no verb keeps `<transport>#<half>`; a recording made before the IPC
  door named its verb states the shorter sites, so it cannot hold a replay made after.
- The id is recursive through the Anchor chain: one unreproduced link anywhere upstream changes it.

**Message producers.** A sent message's producer endpoint is minted at the send
(`Identity#messageSent`) in the sender's current occurrence, at its site (with its verb, if its door
names one); its `SEND` event states the same site. A response's producer endpoint is
minted when its request is received (`Identity#responseEndpoint`: the request scope's role
occurrence, site `<transport>#RESPONSE`, index `[site@0]`, never a verb), and the send reuses it
(`runtime/CausynthTraceRecorder` `RECEIPTS`), so whichever thread sends the response names the same
producer. Two messages carrying one producer endpoint are named as a `LINEAGE_LOST` DIAGNOSTIC row.

**Pairing** (`runtime/Interactions`, in-JVM, each store bounded to 8192 entries by eviction):
`sent` files a message's producer by (transport, correlation, half) and by endpoint id; a receiver's
anchor is looked up there. `exported` files an exported value's producer by VM handle; `carried`
files the producer of each value staged on a message by that message (correlation, half) and the
port, at the message's own outbound door (`SymbolicMessageEnvelope#carriedBy`, called by
`CausynthTraceRecorder#outboundExchange` just before the door drains the envelope), never where the
value was exported: a server's export while it serves a request belongs to its response half
(hdfs-adhoc-07 HG5A: a JournalNode's own export, filed under the request it served, answered that
request's attaches; 855 self-pairings, 57 of 68 paths self-contradictory). `pairing` answers an
attach by `HANDLE`, else -- when the message it received (`MessageDoors#current`) carried an element
for the port -- `CORRELATION_PORT` (that message's correlation and half, and the port), else
unpaired: an element the message did not carry (`SymbolicMessageEnvelope#take` `ABSENT`: a value its
sender forwarded without exporting it) pairs with nothing and is named `LINEAGE_LOST`. A queue item
`MessageDoors#consumed` takes is the message its consumer serves, named by its key and `REQUEST` as
its write sent it (`#stored`), so its elements pair by `CORRELATION_PORT` too. The `WIRE_FLOW`
header does not carry the producer endpoint.

**Interactions** (`contract/Interaction`): (kind, producer endpoint, consumer endpoint), `id =
sha16(kind + producer.id + consumer.id)`, kind `WIRE` (export to attach, `AttachRow#interaction`)
or `STATE` (write to read, `smt/Arms#stateArms`). `smt/Arms` is the one arm rule for COMPOSE and
the flip solver:

- a WIRE interaction's arms are the producer endpoint's exports from runs whose own pairing named
  this consumer;
- a STATE read's arms are Writers_W(l): its observed writer plus every attested writer occurrence
  of the same session that is HB-concurrent with the reader (not the same `threadKey`, not an
  anchor-chain ancestor either way, both chains reaching a `Root`; a `Lost` context is never
  concurrent), one arm per writer occurrence: the observed writer's at the write the read
  observed, any other at its last write of the location; and the writer at version 0, the
  location's INITIAL (`WriteRow#initial`: what it held before every write its log names, a
  constructor's or initializer's store from before the log began, the JVM default, a container's
  members), an arm of its own under no prefix. Every writer but the observed one -- the
  INITIAL included -- is an alternative only where the read could have run right after it, ONE
  rule (`Arms#eligible`, asked by the arms and by EXPLORE's closure and flip query alike): its
  writer HB-concurrent, every write between the two an HB-concurrent occurrence's, none of
  them made under construction (a constructor or a class initializer anywhere on the writer's
  frame chain, which every reader of what it built follows), and no version between the two
  that a read observed without a write row stating it (a writer no row names, which no order
  moves). Locks are not constraints. An activation's `threadKey` is the
  claimed start it runs inside (§6: a queue item or task claimed on a consumer thread,
  `start:<node>|<context>|<frames>`, `ActivationRow#claimed`), else its thread (a thread's own start
  included, `RowRuntime#threadKey`): two items one consumer thread claims (a ZooKeeper server's
  pipeline applying two clients' requests) run in the order their starters queued them, so they
  are compared by their chains, not by the thread.
- an occurrence is attested in a session that has an instrumented activation row for it
  (`Arms#attested`); no witness may move a root inside an unattested arm.

**Locations** (`contract/LocationId`, `KIND/<owner>#<slot>`): the owner of a heap location is the
VM's per-run object id, a static field's owner its class. A state join is per session; there is no
cross-run object identity.

## 5. Attribution: which node

`runtime/Attribution#resolve`, four rules in order: the innermost explicit scope on the thread
(a request, a registered inbound owner, a tick owner, a node startup); else the innermost frame whose receiver is a
registered object, the receiver of the thread's last work entry (`Identity#claimStart`) counting
as its outermost; else, on a thread that claimed no start, the node its creator carried when it
constructed it (`RuntimeTraceContext#inheritedSource`: its explicit scope's, or a node startup's,
below); else the node of whatever started this work: its starter's by these same four rules
(`Attribution.Reference`: the explicit scope and the inherited node as they stood at the start, the
receivers' registration asked now, then the starter's own starter, at most 32 deep). All four failing is `null`, never a guess:
the activation is then attributed to `workload/unregistered`
(`RuntimeTraceContext#activationSource`), so every activation has an address. An activation under
a `Lost` context is a `LINEAGE_LOST` DIAGNOSTIC row (`runtime/RowRuntime#beginActivation`).

The system's test adapter registers nodes through `MessageDoors.registerNode` (anchor plus aliases:
the objects the node runs its work through), `registerSource`, `registerSourceAlias` and
`restartSource` (HDFS `CausynthCluster`, Solr `CausynthSolrCluster`, ZooKeeper `CausynthZkCluster`,
in the trees). Work on no registered node is attributed to `workload/unregistered`
(`RuntimeRegionPlanner.UNREGISTERED_SOURCE`). The runtime's identity tables -- the registered
sources and carried scopes (`RuntimeTraceContext`), the pending starts (`Identity`), the recorder's
object ids -- hold their objects weakly (`runtime/WeakIdentityMap`): a node a test shut down is
collected, and nothing collected is asked about again (hdfs ad-hoc `TestSnapshot` builds 36
clusters one after another; held strongly, they filled the recording's heap).

**Node startups.** A node constructed or restarted inside the window (a startup window, §3, or a
cluster the test builds or restarts once its window is open) runs under the test's request: rule 1
would name the test's client for every thread the test's thread starts for it, and rule 3 for every
thread its constructor creates. A system's cluster adapter brackets each node's construction in
`MessageDoors.beginNodeStartup(kind, role, sourceId)` / `endNodeStartup(token)`, under the name it
registers the node by once built, and a registered node's start in `beginNodeStartup(node)`: a
restart builds the node anew under its name at its next epoch (`restartSource` first; HDFS
`CausynthCluster`: every NameNode, DataNode and JournalNode an automatic `MiniDFSCluster` or
`MiniJournalCluster` builds or restarts). A startup first ends the exchange the thread served
(`MessageDoors#endInbound`): a construction is the test's own work, so the node and its threads stand
in the test's request, not under the anchor of the last response the test's thread received (round
HG4, hdfs-adhoc-22: a response that differed after a divergence re-anchored every later cluster's
build, and 10560 slots were given up at once). Attribution only -- no event, no lineage hop, no flow: the
startup is the node's explicit scope while it stands (rule 1), so what the test's thread itself runs
inside a construction (a NameNode's format and fsimage load) is the node's, under the test's context,
and work started or created inside carries the startup's node in place of its starter's explicit node
(`RuntimeTraceContext#carriedIn`, read by `captureAsync`, `Attribution#capture` and a new thread's
inherited state). Left the test client's, a NameNode's format and image work could never join its
later work: the demand walk crosses writers on one node only (round HN1: 46, 47 and 52's targets on
`auto<n>/client0`). The node is named
from the startup's first moment: bound only once built and registered, what its constructor's
threads did before raced the registration (HBase's HBA2: ZooKeeper callbacks a region server's
construction set up were the unregistered workload's in the recording and the region server's in the
replay, and its seed replay stalled; HDFS round HS1: a DataNode started inside the window ran its
storage checks as the test's client). A startup is construction work, not a turn: a timed wait inside
it is a pause and opens no `WAKE` turn (`RuntimeTraceContext#beginWake`), as inside any scope that is
not itself a turn. Round HG2 (hdfs-adhoc-11, 14): a NameNode's format, inside its startup on the
test's thread, timed out in `FSEditLogAsync$SyncEdit.logSyncWait`; the turn it opened was the lineage
of every IPC handler the constructor then started, and each call that carried no context was served in
that one turn at one address (`OCCURRENCE_ADDRESS_SHARED`).

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
(`RuntimeTraceContext#claimCarried`) and writes a `CLAIM` event. Only an explicit node travels in
the scope (a weaker one made explicit would outrank the work's own frames); the start's reference
(`Attribution#capture`, rule 4) names the starter's node by all four rules, so a task or a queue
item names its putter's node whenever the putter has one -- a DataNode's actor, created by its
startup under no request and so its node by inheritance alone, handed Hadoop IPC's shared sender
work that claimed as `workload/unregistered` until the node registered (round HN1, hdfs-adhoc-53). One exception
(`RuntimeTraceContext#taker`): a client's (`EXTERNAL_APP`) task claimed on a thread that stands in a cluster node is that
node's, under the client's request and lineage -- in one JVM a test may put work straight into a node's executor, and the
work runs in that node's memory: HBase's procedure tests submit into the master's `ProcedureExecutor`, whose step
(tree `CausynthStep`) stood on `auto0/client0`, so the closure, which pairs a read only with writers of its own node
(`RuntimeSelectedRegionFinalizer` DemandWalk), planned none of the master's writers of `RegionStateNode.state`
(hbase-adhoc-15, HP5). A start no hop names captures
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
it, and into the workload's own test class and its nested classes (a root `<test classes>#<class>`
scans that family alone): a test that starts its workers itself gives each its start frame, so two
workers calling one method are two addresses. Unwoven, both inherited the test thread's index whole
(hbase-bugs-backup-lock-reply-lost: `TestBackupManager`'s two `new Thread(r).start()` workers took one
address for their two lock acquisitions, `OCCURRENCE_ADDRESS_SHARED`).

## 7. Doors

### 7.1 Message doors

`runtime/MessageDoors` is the transport-neutral API every system's transports call:

- `outbound(transport, correlationId, attemptId, half, localOwner, scope[, message])`: the
  sender's trace header plus its symbolic header. The trace header is `1|span|epoch|kind|role|id|
  requestKey|requestApi` (`RuntimeTraceContext#header`); a send with no source or request flow goes
  without one and is named as a `MESSAGE_CONTEXT_REFUSED` DIAGNOSTIC row. The symbolic header is
  `CSE6`: the declared rows' values the thread staged, and the message fields of the protobuf
  `message` the door is handed, which it walks (`MessageCodec#send`, SYMBOL-SCOPE §6.3).
  `outboundRequest(..., verb, message)` is the same for a request naming its operation.
- `parsed(message)`: a protobuf message parsed inside the exchange it arrived in; each of its
  message fields' elements is bound to it for the getters that read it (`MessageCodec#receive`).
- `inbound(trace, symbolic, ...)`: ends the exchange the thread served and installs this one until
  the next message or `endInbound`, with the values its symbolic header carried for the attaches
  the thread makes; `keepSymbolic` keeps a multi-message exchange's values.
- `received(symbolic, ...)`: a request taken into the thread's own context, which it does not
  anchor (a DataTransfer op a DataNode's turn received): its values are installed for the attaches
  the thread makes, and `CausynthTraceRecorder#receivedExchange` records its RECV naming the producer
  endpoint it took in (`ScheduleEvent#received`) and its RECEIVE leg; no response endpoint is
  minted, since nothing answers it through a door.
- `setAside` / `restore`: a serving thread that runs an exchange of its own as a client.
- `beginTick` / `vacant` / `endTick`: a daemon turn as a root; a vacant turn is one the recording
  never made, which a replay held and let go only because the run could go no further. A turn, like
  a node startup (§5), first ends the exchange its thread served (a request, §3, ends a received RESPONSE
  only): the turn serves no
  message it did not take in itself. Left standing below the turn, the next message's end of it
  closed the turn too (round HG5A, hdfs-adhoc-21/22/23/25: a DataNode actor built inside the window
  stood in its registration's response when its first turn began; the IPC client ends that exchange
  before its heartbeat, so the heartbeat went out in the test's request and the turn stated no
  `END`).

The Hadoop adapter is `src/shim/java/org/apache/hadoop/ipc/CausynthMessagePropagation`, shipped
with GraphChecker on `system/hdfs`: transports `HADOOP_IPC` (IPC correlation), `HDFS_SASL` (a handshake of
several messages on one thread, possibly opened by a thread serving a request) and
`HDFS_DATA_TRANSFER` (one op, a request on a correlation of its own: `outboundOp`, `inboundOp`). The HDFS trees call
it from IPC `Client`/`Server`, the SASL data-transfer classes and the DataTransfer op's two ends. The IPC server's
handler opens a call's exchange, its carried scope and its inbound, before any of the call's work, the remote user's
`doAs` included (`Server.Handler#work`, `Call#causynthEnter`, on `gc/hdfs-study-r4` and `gc/hdfs-11741-r4`), so every
occurrence a handler runs for a call stands on the call's own anchor, indexed from its inbound; opened inside the call,
the `doAs` region opened first, under the context the Reader carried with the queued call, and only the Reader's and
the handler's start counts told two calls apart (round HG5A hdfs-adhoc-14: one address planned, another run each
replay). The IPC client's requests start at the RPC engine's invoke point (`requestStarting`, §3,
on `gc/hdfs-study-r5` and `gc/hdfs-11741-r5`), which ends a received response before the client's
call; the client's own hand `endInbound()` before its send is gone. So in the Solr tree
(`gc/solr-body`): `CausynthHttp#requestStarting`/`#requestEnded` wrap `HttpSolrClient#request`,
`Http2SolrClient#request` and each stream of `ConcurrentUpdateHttp2SolrClient`'s runner, named by
the request's operation (`CausynthHttp#verb`: its path, and an admin request's action,
`admin.collections:REQUESTSTATUS`: a verb spells no `/`), and its send is `outboundRequest` of that verb, so the Overseer's
extra status polls renumber no other request. The Solr trees call
`MessageDoors` directly (HTTP headers through `CausynthHttp`, ZooKeeper through `SolrZkClient`), and
so does the ZooKeeper tree (`CausynthZk`: transport `ZOOKEEPER`, one `REQUEST` message per client
request, sent where `ClientCnxn` queues it, its header beside the bytes under the session and xid
they carry, served by the server's `PrepRequestProcessor` and `FinalRequestProcessor` stages).
The HBase tree calls it from `CausynthRpc` (transport `HBASE_RPC`, one exchange per RPC call,
correlation `hbase-rpc-<client>-<call id>`, the context in three `RequestHeader` and two
`ResponseHeader` fields of `RPC.proto`). A call's request starts and ends in
`AbstractRpcClient#callMethod` (`requestStarting`/`requestEnded`, verb `<Service>.<Method>`; HBase's
own retries are new calls, new requests of the verb), and the calling thread sends it there
(`outboundRequest` with the request message, before `RpcConnection#sendRequest`), so the envelope it
staged and every element bound to the message are drained where the call is made; the connection's
event loop, which writes the call after its queue, only copies the call's header strings
(`IPCUtil#buildRequestHeader`). A value exported on one thread and sent by another after a queue
therefore needs no message-bound export of its own. The response is received by the thread that reads
it (`RpcConnection#readResponse`: the client's event loop, or a blocking connection's reader), its
message fields bound to the parsed reply (`MessageDoors#parsed`) before the call completes; the call's
callbacks run inside that exchange, which ends when they return. A handler opens the call's exchange
at the start of `CallRunner#run` and binds the request's fields, and `ServerCall#setResponse` sends the
reply with its message.

A DataTransfer op leaves in `Sender#send`, whose SEND names the op's producer endpoint; it sets the
op's correlation and every value the thread exported for the op on the op's trace info
(`DataTransferTraceInfoProto`, in its header's base header, or its own for the two short-circuit
shared-memory ops; `DataTransferProtoUtil#withCausynth` on `gc/hdfs-unified-dtx`). The DataNode
takes it in at `Receiver#continueTraceSpan`, after the op's parse and before any of its fields is
read, inside the op's turn (the exchange a SASL handshake opened ends as the turn begins, and the
op's with the turn). The turn keeps its own `Root:DATA_XCEIVER` address: standing
on the sender would hand the DataNode's occurrences the sender thread's IPC chain, whose counts a
replay does not reproduce (b20h FsDatasetImpl-1843: 15 of 16 such tasks unanswered). The op is a
message for everything else: its header's protobuf leaves pair with the sender's exports by handle,
its RECEIVE binds the receiver's captures to the op's leg so the walk plans the sender (SYMBOL-SCOPE
§4.4), and its RECV names the message that made the turn, which the control producers read as they
read an anchor (§7.3; `ScheduleEvent#received`, `causynth/RecordedMessages#doorsOf`,
`explore/Corpus#startedBy`). The order holds the op's SEND and RECV as slots like any other (§8):
nothing settles one the replay does not make, so a SEND from a sender context the replay does not
reproduce, or a RECV at a DataNode the replay's pipeline does not reach, stalls the order a timeout
and a grace. The op's response and the pipeline's acks carry no envelope: none of their messages is
one a protobuf service carries, so none holds a port (SYMBOL-SCOPE.md §6.2); their fault doors are
SYMBOL-SCOPE.md §4.2's.

### 7.2 Store doors

For a store the nodes share (ZooKeeper in a one-JVM cluster):

- `stored(transport, key, owner)`: a write of `path@version` is a SEND; its staged values are kept
  with the version. It is also a version of the path's `STORE` location (CONTRACT-SPEC §1: owner the
  transport, slot the path as `RunNames` keys it -- `<path>#<n>` from its n-th life on, a version 0
  written once the path stood at a version being a create after its delete (`MessageDoors#life`) --,
  version the store's own): a write row at the
  writer's occurrence in a replay (the admitted activation's, else the one running there, stated as
  an unselected activation), site `<transport>#WRITE:<path, dotted>`, no expression, seq one past
  the VM's last event id, where a concrete target stands (`Identity#afterLastEvent`: a closure cuts a
  writer strictly before its write, and keeps the writer's own last event, its door's fault marker;
  0 with no VM clock: no order check reads it; two versions of one path at one seq are two events,
  CONTRACT-SPEC §2.6); a `STORE_WRITE` trace row naming the writer's
  address in the recording. Every row the engine states of a store or a node's view stands on that
  scale -- a decode's view write, a PROVENANCE site's and a view accessor's STORE and VIEW reads, and
  each schedule event's `vmEvent` -- so a read stated with no VM event since the write it saw is
  never ordered before it (`SlotTable#contradictsOrder`; round Z2L: 78 BLOCKING
  `TOPOLOGY_DIVERGENCE` rows while the reads stood one event earlier -- a PROVENANCE read with no
  VM event since its decode or the store write it saw was stated so too).
- `notified(kind, callback)` + `fetched(transport, key, owner)`: inside a watch callback, the first
  read of a stored version installs the writer's context, with `via` = the watcher kind (and
  `.<n>` from a node's second delivery of that version on; how many deliveries a run takes is the
  store's timing, so CONFIRM names every delivery of one version alike,
  `CausalContext.Anchor#anyDelivery`). Such receipts are unawaited: the work
  they anchor takes no place in the schedule. A read outside a callback is no cause; what it
  fetched is read where the objects it was parsed into are read (below).
- `decoded(transport, key, product)`: the objects a fetch of `key` was parsed into (the adapter's
  product: Solr's `ClusterState.load`, `Aliases.fromJSON`) hold that version (`runtime/Provenance`):
  the product's graph is walked once -- instance fields of application objects, the contents of
  maps, collections and object arrays; no JDK object, value, lambda, synthetic class, engine object
  or inner object's outer one; at most 4096 objects and 16 hops, a walk cut there a DIAGNOSTIC
  `UNSTATED_VALUE` -- with the VM's propagation paused, and each object it meets is registered with
  the version, the first decode keeping it (another version's decode reaching it states a DIAGNOSTIC
  row, counted in `Causynth decoded walks:`, never a re-pin, as are a constructor's holder built from two
  decodes, which keeps the first, and a member the walk could not read); a class's constant (an object a static
  field of its own class holds, itself or as a value of a table it holds: `DocRouter.DEFAULT`, the
  routers of `DocRouter.routerMap`) and a supplier with what it holds (`PrsSupplier`'s per-replica
  states) are no product of the decode, which cannot tell what it allocated: each skip is stated and
  counted. A decode first waits for a write in flight at its path to file (`MessageDoors#filed`,
  bounded and named), so a create's version 0 names the life it opened. A guard that reads a construction-only field of a
  registered object at a `PROVENANCE_SITE` (SYMBOL-SCOPE §5.7) reads that version: a STORE read row
  at the reading occurrence, its symbol naming the version (`RowRuntime#storeRead`); a path rests on each such read its closure made before its cutoff, though no term names it, and CONFIRM holds it to the version the session read (a STATE row, `compose/RestsOn#storeLocations`: a run whose reader read another version does not confirm), compared and ordered by nothing: the store's own turn orders its reads and writes, and a native run's weave states no store write's activation (`explore/ConfirmMain#stateEdges`). The recording
  states each decode's objects by identity (`STORE_DECODED`), which PLAN joins with the objects an
  occurrence read a field on. Each replay's log states the walks' cost (`Causynth decoded walks:`).
- `consumed(transport, key)`: a queue item taken, as `received` takes a request: it ends what the
  thread served and is the message the thread serves until the next (its key and `REQUEST`, as its
  write sent it), its staged values with it; the consumer keeps its own context, and its RECV names
  the item it took in (`CausynthTraceRecorder#receivedExchange`), so the item's sender is a door of
  the message that started the consumer's turn (`Corpus#startedBy`, `RecordedMessages#doorsOf`) --
  of every item a batching turn took in (the Overseer's state writer flushing several at once). A
  RECV a turn makes at its root, before any of its regions opened, names no occurrence: unless the
  turn stands on the item (a request's handler, which the item started), every occurrence the turn
  runs is then a receiver, a door of the item for an occurrence of another turn (its own turn is
  what the item started: solr-18413's Overseer state updates, each one consumer's) (`Corpus#doorsOf`,
  `RecordedMessages#doorStancesOf`) -- the Overseer queue loop's turn, whose ZooKeeper door
  (`markTaskAsRunning`) runs in a region of it, for the task's Runner, which took the same item in.
  Every occurrence of the turn that sent a message is a door of it too: a fault anywhere in the turn
  can stop it short of the send (RestoreCmd's RESTORECORE requests before its ACTIVE offer, their
  failure an exception that crosses the shard handler's executor, which no term names). Each
  narrowing names what it cut, a counted DIAGNOSTIC row (PLAN's plan gaps, EXPLORE's): the served
  occurrence's own turn, the turns standing on the message (its handlers,
  `RecordedMessages#handlerStancesOf`), and a control producer, whose own message's doors are not
  asked (it contributes no value).

A STORE read rests on the write that made its version and on every earlier version of its location:
a store keeps one document per location, and each write modifies the one before it (Solr's state
writer and aliases, every compare-and-set write), the rule `compose.RestsOn#closure` applies to
every location. The closure demands those writers on any node -- a one-JVM cluster's nodes are one
session, whose happens-before spans them -- each with the doors of the item it took in
(`ClosurePlanner#storeWriters`, `#earlierVersions`; PIPELINE §7.2); PLAN admits the same
(SYMBOL-SCOPE §4.4, `STORE_WRITER_V1`). No static candidate: a path is no field a site stores. A
writer that runs no woven region (an updater turn of an Overseer whose code is out of scope) is a
role: passed through to its item's doors, never planned, its own decisions not flipped (STATUS).
- `storing(transport, location)` ... `storeEnded(transport, token)`: a write in flight at one
  location (a sequential create's: the prefix the store completes). The write first takes its turn,
  a `WRITE` event whose site is `<transport>:<location>` (§8), so writes to one location run in the
  recorded order while the prefix holds them and the store decides each race they run -- whether a
  create finds its node made -- as the recording's did (SB19, solr-bugs-reindex-cleanup on `main`: a
  node created the collection's terms node the recording had another replica create, and the shard's
  leader election went the other way). `storingChild(transport, location)` is the same for a write
  that takes or frees a number of its location's parent -- a sequential create (the prefix), a delete
  (the path) -- whose turn is keyed by the parent: every participant of one leader election, every
  writer of one queue, takes its sequence number in the recorded order. The location is keyed as
  every run spells it (`runtime/RunNames`, `contract/RunSpellings`): a name a node has only in this
  run -- its store session's id, its host and port -- that its adapter stated
  (`MessageDoors#spelledAs(sourceId, spellings...)`, only a spelling holding such a name, and each
  such name inside it, as a node name's host and port a URL spells bare; stated again on a node's
  restart) becomes the node's name. The session states them at its close (the manifest's
  `runSpellings`), and an arm's key names a written term's constants and observed values by them
  (`explore.Corpus#programNames`), so a port spelling names its node in every run; an object's
  identity hash as the JDK's default `toString` spells it (`<Class>@<hex>`, `RunSpellings#IDENTITY`)
  stays in the location (two objects' paths are two locations; only an arm's key numbers it,
  `explore.Corpus#handle`); a
  location still spelling a long number or a host and port takes no turn, and is named once
  (DIAGNOSTIC `DECLARATION_MISSING`). Past the cut no slot holds: writes there are ordered only behind
  the prefix's. The store applies a write,
  and notifies the version's watchers, before the write's call returns, so another thread can
  read the version before its writer files it (SOLR-18413 F2: node1's state watchers read the
  routing rule's version while the Overseer's turn was still in `stored`, and their work opened
  no occurrence). `stored` is in flight at its key's location until it has filed the version; an
  adapter opens the bracket before the store's call and
  closes it in a `finally` after `stored`, so the store's own latency is inside it too. A read
  that takes what its write carried (`consumed`, `fetched` in a callback) and
  finds the version unfiled waits for the writes other threads had in flight at the version's
  location when it read -- that location, or a sequential prefix of it, never a parent --
  (`MessageDoors#filed`): the one that made the version files it before its bracket ends. A
  version no such write files was made outside the window or carried nothing; its read names
  nothing and waits for nothing begun after it. The wait is bounded: `FILED_WAIT_MS`, 2 s, while no
  thread making those writes is filing -- a writer held behind the reader before its store's call
  (before a replay's cut a writer may be held at its SEND while a reader waits for it) costs the
  bound --, `FILING_WAIT_MS`, 60 s, while one is (`stored` began: past its store's call, it takes no
  turn before it files, and exporting a document's leaves under the VM takes seconds; solr-18413
  Z2V: an Overseer queue item read 2 s into its filing paired with no write). Past it the read
  names nothing and a DIAGNOSTIC `LINEAGE_LOST` row names the version and the writes still in
  flight. Writes at other locations, of the same transport or not, order nothing.
- `reading(transport, location)`: a store read outside a callback -- whether a node exists, its data,
  its children (the location is then the parent) -- takes its turn as a write does, a `READ` event at
  the same `<transport>:<location>` key (`RunNames#key`, one spelling with the write's and with the
  `STORE` location a version is filed under), before the store's call: it waits behind the write the
  recording made there before it, and the write the recording made there after it waits behind it
  (§8). What a create-if-absent's check, a compare-and-set's version or a client's view of an alias
  or a collection's state finds is then the recording's (solr-adhoc-39, MB23s: the commit's node
  followed the client's view of the alias, which a store read before or after the alias's write
  decided). A read takes a slot only at a location a write of the order wrote (reads of every other
  path take none and count as no step), and never in a timed-wait loop's turn (§8): such a loop's reads
  are its polls, whose count is the loop's timing, and the writes it follows order what it finds
  (`ScheduleLog#heldReads`; SGF7-adhoc-10's seed: the Overseer read `/overseer/queue` 117 times to the
  recording's 91, held at the n-th recorded read's place, 95 let-gos). A `READ` slot holds no frontier: it is never blocking,
  so a read that never comes holds nothing back.

### 7.3 Typed faults

The library catalog's doors and the woven markers are SYMBOL-SCOPE.md §4.2. A marker's branch is a decision of
the occurrence that runs the door; `explore/ClosurePlanner#controlProducer` adds the sender and the
receiver of the message a demanded occurrence served (its `Anchor`, else the message its turn took
in, `explore/Corpus#startedBy`; `#senderOf`, `#receiverOf`) as control producers where a session
recorded a fault decision of them, so their door faults are proposed as flips. PLAN plans the door
occurrences that read a fault marker on the same relation, over the recording's schedule
(`causynth/RecordedMessages#doorsOf`, SYMBOL-SCOPE.md §4.4), so the faults EXPLORE proposes are
minted: one predicate. A door that decided no fault -- unplanned, since it read no marker (a
transport with no woven door in the case's scope), or a role -- is a DIAGNOSTIC row, not a member.

### 7.4 Captures bound to exchanges

PLAN binds each wire capture of an activation to the exchange it ran in
(`RuntimeRegionPlanner#bindObservedCommunicationCaptures`): an OUT capture to the next SEND on its
lane, an IN capture to the latest RECEIVE, rewound to that exchange's first frame.

## 8. The schedule

`contract/ScheduleEvent` = (seq, kind, context, site, k, occurrence, endpoint). Kinds: `START`,
`CLAIM`, `SEND` (with the producer endpoint), `WRITE` (a shared store's write taking its turn before
the store's call, §7.2), `READ` (a store read's turn, at a location a `WRITE` of the order wrote), `RECV`, `WAKE` (a timed wait's timeout; a tick's
begin), `END` (a tick's end), `INTERRUPT`, `PUBLISH` (a store notification put a version of a node's view in force, `MessageDoors#publishing`: at the node's own `<node>|VIEW` stance, site `<transport>:<path>@<version>`, the first of each version -- a watch callback's own events are free, its receipt unawaited, so without it a replay published a version when its timing had it, under the VM after a reader the recording ran after it, SGF2 snapshot-no-active; held, it is taken by the node's publisher, never on the callback's thread, which holds its collection's refresh lock: `Confirmation#publishing` hands a publication whose turn is not due (`ScheduleLog#dueNow`) to the publisher, which never blocks on a turn -- each view's queue head applies when its own turn is due, so two views of one node arriving reversed each go at their turn -- and waits for a turn not due as the order's waiter, where the watchdog sees it and its give-up stops (`ScheduleLog#duePublications`); every turn is settled once the publication is in force (`Confirmation#begin`, `#settle`): a turn due at the callback's door stands in flight from the door, the caller publishes as the system does, and the turn is taken when the callback ends (`MessageDoors#notified`'s finally, `Confirmation#notificationEnded`: Solr's watch callbacks, `StateWatcher#process` and `AliasesManager#process`, end right after their `constructState`, a throwing one included; nothing the system runs is moved or locked differently), a deferred one by the publisher after its apply, an exempt version's given up by name at those points, and the recording writes the event there too, so nothing the order lets go after it reads past it (SGF3 snapshot-no-active: v8's turn taken at the door let the Overseer's task read node0's cluster state before the callback's `constructState`), unless the apply waits at the frontier past `PUBLISH_GRACE_MS` (500 ms) on a lock whose owner chain reaches a thread waiting for its turn (the publisher aside, never through the order's own lock) -- a lock the system's publication takes held by a thread the order holds behind it, a cycle -- when the watchdog takes the turn for it, named (`#publicationBegins`, `#inFlightLocked`, `#heldByTheOrderLocked`; an apply computing or waiting on anything else holds its turn); the site is the path in its store life as every run spells it; when a newer version reaches a node's door -- a notification's, before its own turn is asked, or the system's own publication at once -- its open `PUBLISH` slots of the view at older versions (the system's own: and at that version, the view being at it already; a notification of it that still comes re-points nothing), but those deferred on its publisher or in flight (begun, its callback still publishing it: review SA), are given up by name (`ScheduleLog#publicationReached`), as is the turn of a publication superseded before it applied (`#turnNotTaken`); a pairing's hold wins, the prefix cut before the first decode past the paired version leaving every `PUBLISH` after it unheld, and the paired version's own publication, or the reader's own work's, goes in force at once, its turn given up by name after it; the windows left: the system's own publication at once, which its caller makes, gives the node's open turns up at its door, before it is in force -- on its own thread or on another's (a `forceUpdateCollection` on the Overseer's thread gives node0's open turn of the collection up, and what that turn holds back may run before the refresh's `constructState`) -- since its in-force point, the refresh's end, may lie past the same thread's next turn (`forciblyRefreshAllClusterStateSlow` fetching the next collection under the update lock); and the backward window of a turn taken at its callback's end -- what lands between the publication's in-force point (its `constructState` writing the cluster state) and the settle: the rest of `constructState` (`notifyStateWatchers`, whose watcher may count down a `waitForState` latch, so the woken thread's next event runs before the turn its recording made it wait for), the update lock's release, `publishIfNewer`'s `notifyAll`, and the settle's own wait on the order's lock -- each an event the recording ran after the turn, now able to run before it; the exact in-force hook needs a tree point after `constructState` (TODO Solr §3o)). A tick's `WAKE` is computed at its begin and written as
the turn's first event is admitted, before it, in both passes (`ScheduleLog#turnBegun`,
`#takeTurnWake`: at `observe`, at a held timed wait's admitted or timed-out `WAKE`; asking whether
the turn is vacant is that first step), its `END` only if its `WAKE` was: a turn that makes no event
holds no slot, and its begin shows its thread away from the frontier (`ELSEWHERE`), so a spinning
loop defers no stall. In a replay the turn's first event first takes the `WAKE`'s slot; what the turn
computes before it makes no event and is not held. `context` = `<node>|<ctx render>[|<start frames>]`
(the claimed starts' levels from the scope base, each start's own frame after the starter's frames
it was filed with) (`ScheduleLog#contextOf`, `Identity#handoffs`). Where a consumer claimed work
(a queue item, or a task taken on another thread than its starter's) the levels start at its
outermost such claim (`State#consumedStart`): a queue item's claim carries its putter's scope
(§3), so the consumer's own start and the frames it inherited -- which IPC handler or reader took
it -- are the queue's scheduling, no part of the context (hdfs-adhoc-46: which handler claimed a
call moved its `CLAIM`'s context). A task claimed on a pool's
thread stands on its starter's frames as levels of its claim; a started thread stands on the frames
it inherited from its creator (§6) and adds its start frame alone, so its inherited frames above its
scope base are its starter's frames here, by their call sites alone (their `k` counts how often the
creator came there: the k-th call of a poll re-creating an idle IPC connection, which one thread's
events must not depend on): two threads started through one utility (Hadoop's `Daemon.start`, each
call a level of its own, both starts its 0th) after one RPC returned differ by the sites they were
made at (hdfs-adhoc-02: the LeaseRenewer had taken the DataStreamer's addBlock slot). Two threads
one site made in two calls of one method, each started from a level of its own, share a context. Only the schedule's context strings carry this; occurrence and endpoint ids, and the
question shapes (`ContextShape.Stance` reads node and causal context only), do not; a recording
made before this rule states shorter contexts for such threads, so it cannot hold a replay made
after it (every campaign records and replays with one frozen jar). `k` counts events per (kind, context, site). A
`Lost` context, a context anchored by an unawaited receipt, and one anchored by a message this run
stated no `SEND` for (`ScheduleLog#unordered`, `#SENDERS`: sent before the window, from a Lost turn,
or from a context that makes none) make no event: the order cannot hold what a cause outside it
causes (hdfs-adhoc-19/35: a DataNode's block report went out before the window, and its reply, with
the NameNode's commands, came inside it). A response stands where its request was received, so a
receipt in such a context answers with no `SEND` (`CausynthTraceRecorder#outboundExchange`), and
what the reply causes makes none either. The stances are a bounded store (`Interactions#LIMIT`): once
it dropped one, a miss may be a dropped sender, so that sender is unknown, its context ordered, and
it is named once (`schedule-sender-unknown#<endpoint>`). `mark` rows state
where each occurrence opened (the cut of a prefix focusing it); `{mark: WITNESS, at}` states the run
was cut at its witness; `{mark: INVOCATION, of}` which invocation of a parameterized workload test
the run is (`runtime/JUnitInvocation#stated`), written before the window and handed on with every
order, so a replay held to a run of another invocation is refused by name (`ScheduleLog#invocation`).
`{mark: STARTUP, step, who}` states one taker completing a startup step an adapter names (the HDFS and HBase
trees, through `system/hdfs`'s `MessageDoors#startupStep(step, who)`/`#startupDone`; no Solr adapter names one): a step that builds state a replay reads and
that no slot orders, before the window or inside it (the NameNode's IPC handler takes no slot between
its `RECV` and the write lock its step runs under); `who` names the taker the same in both passes.
Marks are written in completion order and handed on with every order (`SchedulePrefix#write`). A
replay holds every taker at the step until every pass marked before its own (a taker's n-th pass is
its n-th mark) completed it, whatever either run's window -- two passes' windows may open at
different points of the start-up (hdfs-adhoc-43, round SS5: two DataNodes added in the other order,
no hold) -- at most one schedule timeout, then gives the missing ones up by name
(`runtime/StartupOrder`, a `SCHEDULE_DIVERGED` DIAGNOSTIC `startup#<step>`; an interrupt ends the
hold by that name too). Inside its own window a held thread is away from the frontier
(`ScheduleLog#elsewhere`), so a hold defers no give-up.
HDFS's step is the NameNode adding a DataNode (`FSNamesystem#registerDatanode`, around its write
lock), named by the DataNode's UUID, which its seeded draw makes equal in both passes: the topology
orders DataNodes as they are added, and block placement picks pipelines by position there
(hdfs-adhoc-01/43).

`runtime/ScheduleLog` records in both passes into `schedule.jsonl`. In a replay it also holds the
order:

- the order is the source session's prefix (`CAUSYNTH_SCHEDULE_PREFIX` / `causynth.schedule.prefix`)
  then its rest (`schedule_suffix.jsonl.gz`), cut by `explore/SchedulePrefix` at the task's target;
- an event takes the earliest open or given-up slot of its key that its own occurrence made, else
  the earliest of its key (`ScheduleLog#slotOf`: two concurrent RPCs under one context share a key
  and must not swap slots); with none it runs free. In a timed-wait loop's turn (`Root:WAKE/<wait>#k`)
  the key's context is the turn's family, its number left out (`Root:WAKE/<wait>#*`, node and start
  frames kept, `ScheduleLog#turnFamily`), and the event names no occurrence: k counts the node's wakes
  of that loop, a timing fact (the owner's identity rule, semantic counts only), and an occurrence id
  digests it, so the replay's loop takes the recorded turns' slots in order whatever turn it is at,
  a recorded turn's occurrence closing settles none of them, and a waiter there passes them by its
  family as a waiter no occurrence names does (SGF7-adhoc-10's seed: the Overseer's peekElements loops
  woke 348 times to the recording's 82, and 113 of its 172 `SCHEDULE_DIVERGED` rows stood on such a
  turn). The rows keep the run's own contexts and k. A slot
  before the cut, or a `WAKE` slot anywhere, is held until every earlier slot is settled. An
  `INTERRUPT` slot holds nothing and is in no later event's way, as an open `WAKE` is not
  (`ScheduleLog#heldKind`, `#blocking`): whether an interrupt is observed, and in which context, is
  the state the interrupted thread stood in when another thread's call came (a Hadoop IPC sender
  idle between calls stands in its last call's claim), and the interrupter's own events hold the
  order; it takes its slot if it comes;
- a `WRITE` never passes an earlier held write to its location (`ScheduleLog#conflictLocked`): one
  with a slot that holds is due only past it anyway; one whose slot holds nothing (past the cut), or
  with no slot -- a write the recording did not make there: a create-if-absent another node's write
  found made, a retry, an extra sequential create -- waits for the write that was next there when it
  first asked (fixed then, never every later write there), at the slot after it, until that slot is
  taken or given up. When such waiters are the earliest, a stall gives up that one write alone, never
  the run of other events before it, and it counts as no stall past the cut. A write that never comes
  costs a stall, never the run: on `solr-bug-reindex` a given-up write still conflicted (a LATE state,
  never reversed), and SOLR-18413's seed replay stalled 103,812 times -- a core-admin CREATE's queue
  write waited behind the Overseer task's, which the Overseer makes only once its
  `waitForCoreAdminAsyncCallToComplete` poll sees that CREATE complete; the poll's requests are that
  write's owner at work, so the cycle costs the stall's ceiling (`CEILING` timeouts, 120 s at the
  default), then goes. Such a waiter passes none of its own context's slots there (where it waits is
  the other write's place) and is never let go; it waits for no later write while its own context holds an open
  slot before that write, which only it makes (solr-adhoc-19, round MB14s: a node's extra compare-and-set retry at
  its terms node waited behind another node's later write there, and its eight registration slots stalled one by
  one; 39, MB18s: 45 such writes given up one by one, behind writes up to 970 slots past the frontier);
- a `READ` is held by its location alone: it waits while a write the order makes there before its slot is
  open and holds (the earliest such), and a `WRITE` waits so behind the reads there as behind the writes
  (`#conflictLocked`; reads never wait for reads), with the write rule's owing exception. Its slot is never
  blocking (`#blocking`), so the frontier passes it. The read's wait is a held one: while the order moves it
  waits for its write; a grace into a stall it is let go, the write's slot kept (`#letGoHeldLocked`): a
  read's k-th slot is its context's k-th recorded read there, and a context that reads more often than
  recorded -- a poll, a cache refresh -- waits for a later write than its own, which may wait on the reader
  (solr-adhoc-39, MB29s: 37 such waits given their writes up, 447 s, and 145 write conflicts 1,710 s). A
  write behind a read that does not come gives that read up a grace into the stall, not a timeout. A read
  with no slot runs free. Only the reads a run's recorded placement decides take slots: in a run the model
  orders (a world's planted pairings, CONFIRM, a reproduction's plant: `ScheduleLog#readsHeld`) the reads
  past the cut take none, and the model's `ORDER` rows place them (PIPELINE.md §5);
- while the prefix stands, a `WAKE` with no slot is held too (`ScheduleLog#waitsAtLocked`). One the
  recording never made waits at the cut. One past its recorded count (a loop polling longer than
  recorded) waits until its context's next slot is due, then polls once per move of the order
  (a settled slot) since its previous `WAKE`; the slot its last recorded `WAKE` took counts, so
  the first poll past the count goes at once. A poll whose context's next slot is the frontier itself
  owes it and goes with no move: held, it held the frontier until the watchdog (solr-adhoc-19, round
  SG1: `ZkController#waitForCoreNodeName`, 66 stalls of 15 s). A loop that reads a CLOCK root goes as soon as its
  slot is due: `runtime/ClockLoops` finds, on the waiting thread's stack, a method in which the
  scope map declares a CLOCK root (by method, so a clock read in a callee that returned before the
  wait is missed; the methods are installed from the rows the session reads when it opens,
  `GuardedStoreSites#install`, never at a wait, where reading the map held a thread's first wait
  seconds mid-run and timed out an IPC caller's hand-off to its sender). An event of a timed-wait loop's turn
  (`Root:WAKE/<wait>#k`, `ScheduleLog#timedWaitTurn`) whose slot is not yet due waits at it as such a poll does, held:
  it takes its family's slots in order, and a loop that makes more of its events than recorded finds a later turn's;
  let go, it takes that slot, a `WRITE` still behind an earlier held write to its
  location (solr-adhoc-39 MB29s, before the family key: the recording made 106 turns of the
  Overseer's `ZkDistributedQueue.peekElements` loop, the replay 512, and a queue write in replayed turn #88 waited at
  recorded #88's slot and, as the earliest waiter, bounded a give-up of 4251 slots). The watchdog lets held waits go
  when the order stalls; a released timed wait still waits out its own deadline. A held wait bounds no give-up, at its context's slot or at the line: with only held
  waits waiting it lets them go again, a grace apart, whatever computes (solr-adhoc-13, round MB6: a replica poll held at
  the cut bounded a give-up of the 4560 slots before it; 18413's seed ps1p: a test polling RequestStatus past its recorded
  count waited a timeout a poll). An IDLE stall -- no CPU look since it began saw anything compute -- stands a grace,
  not a timeout: with every thread waiting, what the frontier waits for is held by the order itself (ps1p: a
  MigrateCmd sleep polled once more than recorded and its WAKE waited at the later slot its key found, while the
  frontier was the CLAIM of the work that thread starts after it; each such event came only after its give-up, 13
  stalls of 15 s, 32% of the window with no workload thread runnable). The slot a stall would give up first -- the one write or read a conflicted
  write waits behind, else the frontier -- stands a grace, not a timeout, when it is a `READ` or its context family
  -- its node and causal context, a root's turn number, an anchor's endpoint and the start frames left out -- missed
  its event in a stall before: that family diverged from the recording (round SG2: 69 of solr-adhoc-38's 138 give-up
  stalls, 63 of 19's 70, stood on a context that had failed one; MB21s/MB22s: 34 of 10's 58 and 26 of 31's 69 on
  another turn or anchor of a family that had; MB29s: 102 of 39's 145 conflicts stood the timeout while the family
  was judged by the waiting write's context, not the one it waited for). Past the cut a `WAKE` with no slot runs free, except in an
  order whose run was cut at its witness: that run's log states it (a `{mark: WITNESS, at}` row,
  `ScheduleLog#witnessed`, handed on in the rest by `SchedulePrefix#write`), it made nothing it does
  not list before the witness, so its order ends there and a `WAKE` with no slot waits at the
  order's end, not its cut, until every non-`WAKE` slot is settled (`ScheduleLog#line`; CONFIRM's
  unheld order included). Only a `WAKE` comes unbidden (a timer); any other event the order lacks
  follows a cause the order holds, and runs free;
- settling: a closed occurrence's untaken slots are dead (a timed-wait turn's slots name no occurrence), and an event of a key whose slot died runs free: the
  order no longer holds its place, so it is neither a write the recording never made there nor a poll past its
  count (an occurrence's id can name other work in the replay: solr-adhoc-19 MB8s, the Overseer's state.json
  write, its slot dead with the region its turns shared in the recording, waited behind its own write 110 slots on); a turn's `END` gives up what the turn did
  not do; a waiter gives up what its own occurrence did not make before its slot. A waiter no
  occurrence names gives up the earlier slots of its own exact context, no occurrence naming them,
  at any kind and site it made since it last entered that context (`ScheduleLog.Made`), so the rest
  of a loop it left early is given up (hdfs-adhoc-44: a test's wall-clock poll made 8 of 171 recorded
  RPCs); never an event or a slot an occurrence names. Threads an unwoven starter started share their
  creator's context, so each such give-up is a named `SCHEDULE_DIVERGED` DIAGNOSTIC
  (`schedule-passed#<slot>`, with how often it fired in that context), counted in the progress line;
  a given-up slot is still taken if it comes, and that late take is named
  (`schedule-passed-late#<slot>`). The watchdog
  watches the order's frontier (`ScheduleLog#firstBlocking`: the first open slot that is no
  `WAKE` or `INTERRUPT`), which every wait for a slot or for the line waits on. It acts once the frontier has
  stood the grace (`LET_GO_GRACE`, 2 s) when nothing has computed since the stall began, or
  `causynth.schedule.timeout.ms` (default 15 s) when something computes, or eight
  timeouts (`CEILING`) whatever threads do, both counted from the frontier's last move or its
  earliest current waiter's arrival, whichever is later (`ScheduleLog#stallSinceLocked`): the
  frontier owes nothing to a wait that has not begun. A WRITE WAITING ONLY BEHIND READ SLOTS stands a
  grace, never the computing deferral to `CEILING` (`ScheduleLog#behindReadsOnlyLocked`): a read's slot
  holds no frontier, and a reader computing elsewhere (solr-adhoc-31's test client polling past its
  recorded read) held the write 16 s at each such read. A slot taken past the frontier (past the cut
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
  first lets the waits held without a slot go -- a grace into a stall nothing computes toward, before
  the timeout (round SG1: 92 stalls across six Solr study checks each waited a timeout to let a held
  wait go) --; a grace (`LET_GO_GRACE_MS`, 2 s) after the timeout (a grace in, when the stall is idle) it gives up
  every open slot before the earliest waiter that waits for a slot. That is one let-go per
  frontier: a slot taken past it earns the held waits no second one, which would hold the give-up
  off for as long as anything ran elsewhere. A poll held past its count stands at a due slot and
  waits for no slot's event, so it bounds no give-up; when only such polls wait, they are let go
  again, a grace apart. A let-go does not restart the stall's clock for the waits that remain: a
  wait for a slot is held at most `CEILING` timeouts and a grace, and an event that never comes,
  with nothing computing toward it, costs about two graces. After two give-ups past the cut
  the rest is released. Each let-go and give-up is a `SCHEDULE_DIVERGED` DIAGNOSTIC row. A held
  timed wait asks for its turn once a quantum and spends the quantum in its own wait, before its
  deadline and after it (`ScheduleLog#timedOut` asks, never waits): the monitor or lock it waits on
  stays released until its `WAKE` is written, as the JVM's wait returns only then (hdfs-adhoc-19:
  a timed-out `waitTillNextIBR` WAKE held past its count kept the IBR manager's monitor, and the
  DataXceiver whose block notify the order waited for blocked on it);
- an obligation's replay is held to the schedule of the session whose path it flips, cut at its
  target occurrences (`explore/ObligationSolverMain`, `SchedulePrefix#write`), and inherits that
  session's world (its flips and planted values); flips are cut only from ADMITTED sessions
  (`explore/ObligationFactory`). CONFIRM writes the selected session's schedule unheld
  (`explore/ConfirmMain`, `SchedulePrefix#write` with `held` false): every event is rest, so only
  a `WAKE` still waits for what it followed, and the model's order is held by the `ORDER` rows of
  its expected edges (`runtime/Confirmation`, PIPELINE.md §10): an activation held where it runs,
  a task its executor handed to a worker of its own included (`ActivationRow#claimKind`
  `HANDOFF_TASK`: a `ThreadPoolExecutor` on a `SynchronousQueue`, run on that worker, Solr's
  Overseer command Runners), except a queued task, a queue item, a hand-off task that took work
  another thread started on its thread -- any queue item no named start filed among it
  (`Identity#servingTasks`, stated in the session's manifest at
  its close: a ConcurrentUpdate client's Runner polling its update queue, the take in a callee
  that returns) and claimed work of no stated kind (§4's `threadKey`), which held there would hold
  every item queued behind it: it is held at the send that started it, its anchor's producer
  (`Confirmation#submitter`), up the chain while that send is such work too, and with none an
  `ORDER_UNHELD` names the claim's kind. A hand-off task held in place holds what it holds there:
  an Overseer command its `LockTree` lock, so a command of an overlapping lock ordered before it
  stays parked, and its worker the pool's room (an `AbortPolicy` pool past its maximum rejects the
  next submission); both end at the order's timeout as an order not held in time;
- `runtime/TimedWaits` replaces every timed wait in both passes; under a held `WAKE` slot the wait
  ends at a real signal, or takes its `WAKE` slot when the slot is due and then returns no sooner
  than its own deadline (`TimedWaits#outlast`): a `WAKE` is a timeout, the recording's wait ran its
  whole time, and a `WAKE` is never sooner than recorded, its wait's own duration included. The
  order moves on at the slot; the rest is spent in the wait's own primitive, out of any signal's
  choice, an interrupt kept pending. Code that reads the clock after the wait sees at least the time
  the recording saw (hdfs-adhoc-29/30, round HL1: a DataNode actor's `waitTillNextIBR` (heartbeat
  interval 1 s) ended at its slot before its deadline, the next tick found its heartbeat not due and
  sent none, and the NameNode made the other DataNode the recovery's primary, so the declared
  occurrence never ran). A woven notify marks the longest-standing wait.

## 9. Selectors

A case names its target occurrence (`declared_target_occurrence`) as a selector
(`contract/Selector`), `<node>#epoch<N>/region/REGION.x[@<src>#epoch<N>/<api>]#k`, or as `first`,
the first observed occurrence of the declared target site in the recording
(`plan/RuntimeWorkflowDiscovery.FIRST`; a case stating none is refused at PLAN). The recording's aggregation
resolves it once, against the target occurrences it observed in recorded order whose chain the window
holds back to its root (`RuntimeWorkflowDiscovery#declaredOccurrence`: the k-th a selector matches, by
`SelectorResolution`'s rule; the chain over the recording's senders, `causynth/RecordedMessages#shape`, by
`contract/ContextShape#rootedInWindow`, the rule a replay's answer is held to), marks that occurrence's
plan row, and plans only the question `(r,c)` around it. A target whose shape has an unknown hop -- a
message sent before the window, or one whose sender nothing names -- is never the question: the window's
order does not hold that message, and one sent before the window a replay answers inside or before its
own window as its timing falls (round HG2's hdfs-adhoc-19: the
DataNode's first block report, sent before the window, was answered inside the recording's and before
the replay's, so `first` named a finalize command the replay ran unrecorded); it still seeds the walk
when its shape is the question's, and with no other target the aggregation refuses,
`DECLARED_TARGET_BEFORE_WINDOW`, naming each with its shape. The walk's origins are the target
occurrences of its region and node whose context has its shape (`contract/ContextShape#sameQuestion`,
the rule `explore/Branches` stops replays by), at any index (SYMBOL-SCOPE.md §4.4). Every stage after
PLAN reads the resolved address. `plan/SelectorResolution#resolve` takes the k-th seed activation a
selector matches (region, and the anchor's api when given); an already-resolved address passes
through. No match yields a degraded address, reported downstream as `DECLARATION_MISSING`.

**A replay's answer.** One woven entry per root hook group (`plan/ExecutionTask#rootHookGroup`:
region, root method, a loop-body root's loop) offers each invocation to every task of its group, and
a replay admits a planned task by its whole address, id against id
(`runtime/ConcolicTaskPlan#select`), minted at the node the attribution rule names (§5), as the
recording minted it; nothing else stands in for where it ran (sweep `b20h`: a test thread calling a
NameNode's `FSNamesystem#startActiveServices` or a DataNode's `BlockPoolTokenSecretManager#get`
runs in the test's own scope, at the client in both passes, and a second rule that took the
receiver's registration for where it ran refused it). Every planned occurrence is also answered by
its shape. PLAN states on each plan row its context's shape over the recording's senders
(`contextShape`, `causynth/RuntimeSelectedRegionFinalizer#stateShapes`, `RecordedMessages#shape`), its
recorded root call (`rootCallId`) and the ids of the other occurrences the recording opened in its
region on its node under that shape (`recordedBeside`). **The order rule:** an activation takes the
task whose address it ran at; else the earliest task by recorded root call, of its root hook group,
region and node, not yet live or done, whose shape its own context has hop for hop
(`ConcolicTaskPlan#earlier`, `RuntimeTask#answers`), so a run's activations of one shape answer
the planned tasks of that shape one to one, in order, and never two tasks one activation nor one
task two activations. An activation so answering must also pass three tests (`#answeredHere`): its
context is one no task of that root plans an occurrence of the region in (`ConcolicTaskPlan#occupies`:
not its address, and not another invocation under the same anchor, which is the planned
occurrence's; hdfs-11741 K2: the second `handle()` call of one balancer handshake, under the anchor
of that handshake's planned first call, answered the declared second handshake, which then ran
unplanned), its address is none the recording opened itself (`RuntimeTask#recorded`: an activation at
one of them is that occurrence, whatever it serves this run; accept-SB2: the Solr Overseer's first
task, the collection's CREATE, took the address of the declared second, the REINDEX, whose own entry
then ran unplanned), and its entry opened its own occurrence; its context, shaped over this run's
senders (`runtime/ScheduleLog#shape`: each producer endpoint's SEND stance), reaches a root
(`ContextShape#answers`: no unnamed hop, no `Lost`). The occurrence it opened then takes the planned
address (`Identity#answer`): its rows, endpoints, decision ordinals, schedule mark and close state
it, so every later stage reads the planned address as before, and a DIAGNOSTIC `ADDRESS_UNSTABLE`
row names the address the run computed (`RowRuntime#answered`). A task answered so is done: a later
activation at that task's own recorded address runs unplanned, since the task took an earlier
activation of its shape (the replay ran one more activation of that shape before it than the
recording did). An occurrence a replay exposed (GROW) states no shape and is answered by its address
alone. A planned loop body is asked where its occurrence opens, at its loop root's enclosing entry
(`ConcolicTaskPlan#addressLoopRootInvocation`, the same rule, `#answeredHere`), since no root entry
admits a body: the entry binds the task (`RuntimeTask#claimsEnclosingInvocation`; a task bound to
another entry answers no other), its bodies run under it, and the entry's occurrence takes the
planned address there, once (`LoopAccounting#enterLoopRoot`; hdfs-adhoc-29: a block recovery's
worker under the response of another DataNode heartbeat than the recorded one). Which
turn of a daemon carries another node's asynchronous work is that node's timing, which no schedule
holds: in round `a40h` a NameNode command (block recovery queued by the lease monitor, replication
after a volume removal) rode a DataNode heartbeat other than the recorded one (#4 for #3, #8 for #6),
so every anchor below it differed in the root's k alone and the target was never admitted; in round
HG5A hdfs-11741's DataNode ran the NameNode's key update (`BlockTokenSecretManager#addKeys`, the
`allKeys` writes the witness reads) under another heartbeat than the seed's, outside every region,
so its reads were marked incomplete in 169 of 170 focused sessions; two recordings of one workload
differ the same way. A GROW does it to every replay after it: a region woven since the seed opens
occurrences of its own, so every send under it, and every anchor below, has new ids, and no planned
address there recurs. The answered occurrence's consumers then pair with that chain's producers, not
the recorded chain's: the slot table takes them as growth beside the planned occurrence's slots,
never as replacing them, whichever session lands first (PIPELINE.md §7.1 step 4; hdfs-11741 V4, whose
declared balancer handshake was answered by the other move's). Where the model's arm came from such
a session, CONFIRM takes a delivery into the anchor from any producer that answers the model's
producer's question -- the same site, site index and attempt under a chain of the same shape -- and
still holds it to the model's value; each substitution is a named `ADDRESS_UNSTABLE` row (PIPELINE.md
§10; hdfs-11741 V6: which balancer dispatcher iteration carried the second move to dn1 is the
balancer's timing). A delivery into another answered occurrence is compared by its producer as
recorded: no model value holds it.

## 10. Pass equality

The address is one function of one input set in both passes. The hooks that push a frame or count
an event (`startWork`, `claimStart`, `endClaim`, `claimItem`, `enterMethodFrame`, `exitMethodFrame`,
`throwMethodFrame`) are
in both hook catalogs (`CausynthPipeline.HookCatalog#shared`); every site string is stabilized once
by `contract/JvmNames#stable` (reflection accessors and lambda proxies lose their JVM-minted
counters; a desugared lambda class is named by content in every weave, `LambdaClassNames`);
randomness is keyed by the schedule context (before the window by node and handoffs), site and
count, never by an occurrence a GROW may rename, equal in both passes where one thread alone draws
under that key (SYMBOL-SCOPE.md §4.5).

## 11. Current limits

- The anchor is found through JVM-global tables (`Interactions`, `MessageDoors` stored versions);
  the trace header carries no endpoint, so a context crosses only between nodes of one JVM.
- `Interactions` evicts past 8192 entries; a receipt whose sender was evicted or never filed gets
  no anchor, and its work takes a `Root` or `Lost` context instead, named by a `LINEAGE_LOST` gap
  on the receiving occurrence with the eviction count (`RuntimeTraceContext#unanchored`).
- A different number of calls at one site on the index path moves the index; root `k` counts
  arrival order across threads of one (node, role, api); a pre-window turn is `Lost` and outside
  the schedule.
- An occurrence answered by its shape (§9) states the planned anchor, which that session never sent:
  it names no sender or receiver of it, so EXPLORE finds no door of the message the run's
  occurrence actually ran under (`explore/ClosurePlanner#controlProducer`). An activation the
  recording never made, of a planned shape, takes that shape's earliest open task.
- Contexts and anchors exist only where a transport calls the doors. A DataNode's DataTransfer op
  is a tick root, made by the op only through its RECV (§7.1); on a tree without the op's envelope
  (`gc/hdfs-unified`, `gc/hdfs-11741`) nothing names the op and its header's leaves pair with
  nothing; Solr's Overseer queue turns keep their own context; ZooKeeper watch work is outside the
  schedule.
- Threads started inside unscanned libraries have no start frame and inherit their creator's
  scope; pools other than the three in `PoolWorkers` are not recognized; timed waits outside the
  `WorkStartSites` list (`CountDownLatch.await(t)`, `Future.get(t)`, `Thread.join(t)`, ...) run on
  the wall clock.
- An unreadable schedule prefix lets the replay run free, stated on stderr only; a malformed
  timeout takes the default.
- Only a restart the workload reports through `restartSource` starts a new epoch.
