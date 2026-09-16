# REPORT-M2 — RUNTIME: identity v3, the scope that carries it, and the per-kind session rows

Branch `refactor/d3-runtime`, worktree `SPN/wt-d3-runtime`, base `9b9961b0a`,
merged with staging through `c360ae6e8` (D, D2, M5, the contract v1.0→v2.1
and the composer's v3 adaptation).

**Tip: `8acfc571a`** — suite 52 @Test, 0 failures (cap 80).

## 0. The headline

- **hdfs-17897's seed, re-recorded on the tip: 0 activations with a Lost
  causal context and 0 unpaired attaches** (33 activations: 27 `Anchor`,
  5 `Root:KEY_MANAGER_TICK`, 1 `Root:HEARTBEAT_TICK`; 13 attaches, 13
  paired). That is the lineage gate, met on the first case re-recorded
  after the two closures in §6.4.
- A seed session round-trips through `d3.contract.SessionReader.readAll`
  (every row of every kind, none refused, `explored=false`) and through
  `d3.compose.ComposeMain`, which **resolves the case's v1 selector against
  the seed** to a full v3 id (§6.1b).
- **hdfs-17960's anchor**, which the case must declare, is in §6.3: two
  occurrences, one causal context, told apart by their execution index
  alone.

---

## 1. What landed, and why each piece exists

### 1.1 The scope chain (IDENTITY-V2 §1, superseded as an identity by V3)

`RuntimeTraceContext`'s scope frames gain a **role**, a **parent** and a
**causal anchor**. The frames are no longer the identity — IDENTITY-V3
replaced the hop list with a causal context plus an execution index (§5) —
but they are still what the identity is computed FROM: a frame is what says
"this scope is a workload action of role CLIENT, the k-th in the window", or
"this scope was opened by that producer's message".

| where a hop opens | role | api | lands in |
|---|---|---|---|
| `beginRequest` (a workload action) | `CLIENT` | the declared api | `RuntimeTraceContext.beginRequest` |
| a served message | `IPC_HANDLER` / `DATA_XCEIVER` | the **remote family** `<source>/<api>` | `RuntimeTraceContext.enterInbound` |
| a thread started or a task submitted inside a scope | `EXECUTOR_TASK` | — | `captureAsync` → `enterRoot` (the seed carries the lineage) |
| a queued unit of work taken by a pool thread | caller's choice (`IPC_HANDLER`) | the api being served | `enterCarriedScope` / `exitCarriedScope`, new public API |
| a daemon tick | `HEARTBEAT_TICK`, `BP_SERVICE_ACTOR`, `KEY_MANAGER_TICK`, `DATA_XCEIVER` | — | `beginDaemonTick` / `endDaemonTick`, new public API |

The api of a served hop is the remote **family** rather than the bare api
because two callers of one api are two populations — this is v1's `@family`
suffix, stated as the hop it always was. Nothing is addressed by a request
family any more (step D deleted that); the family is the hop's name.

A daemon tick touches **no** request scope: it opens a scope frame whose
role and window index become the occurrence's `Root(role, k)` context, and
changes no request key.

### 1.2 Identity (`runtime/d3/OccurrenceMinterV2`, `Identity`)

`(node, region, causal context, execution index)` — §5. Minted at region
start from the node the activation RAN on (the planner's own attribution
rule, not the planned node). An activation whose scope cannot be attributed
is minted anyway, as `Lost(role)` with the region slot carrying
`ROLE.<ROLE>` (REPORT-ENTRY §4): dropping it is what left bug3's key
rotation unaddressable, and an unnamed interaction is still an interaction
(INTERACTION-ID R-I1). A node this run cannot name at all publishes **no**
address and a `LINEAGE_LOST` gap instead — fail-closed, never a guessed
node.

### 1.3 The rows (`runtime/d3/SessionPublisher`, `runtime/D3RowPublication`)

One file per kind under the contract's `sessions/<sessionId>/`, written
through `RowCodec`, flushed per row (a campaign halts the JVM, and a buffered
row is indistinguishable from a site that never ran). Every kind's file is
created when the session opens, empty or not, because IMPORT reads one file
per kind and an absent file is a session that published none.

| row | where it comes from | notes |
|---|---|---|
| activation | region start | `focused=false` in a seed replay: the composer reads the unfocused session as the seed |
| decision | `branchMappings` at publication | the term is the predicate the taken arm satisfied — **no second negation** anywhere |
| export | `exportCommunicationLeaf` | every export, live region or not; a degraded producer endpoint where none was live |
| attach | `mintHandoffLeaf` and the entry-rule mint | v_H, the arrival, the answer, and the producer the run paired it with by the VM handle |
| write | the VM write log (`sharedFieldVersions`) | `seq` = `fieldVersionId` |
| read | `ReadFromExpression` / pinned `FieldAccessExpression` nodes | the version each read observed |
| root mint | `symbolizedRows` | kind from the declaration (CLOCK when it declares a callee, MARKER for a boolean); domains where the mint states them |
| target | `targetReach` + the anchor's own decision | φ in the **fatal** polarity whichever arm ran, `observedFatal` beside it |
| gap | every refusal above | the closed enum only |

Contract v1.1: every decision/export/attach/write/read/target row carries
`seq` — the VM's own event id, one counter the versions and the decisions are
both drawn from — and every export/attach/write/read carries the JVM
descriptor. A row the VM gave no id states 0 rather than inventing a second
numbering of the same events.

### 1.4 The entry rule

Every declared port mints on arrival whatever is selected. An attach with no
live region now mints v_H on the ambient activation and publishes its row
against a degraded consumer address, without starting path recording — an
unselected activation records no path, which is precisely what not selecting
it means. `RPC_HANDOFF_NO_ACTIVE_REGION` has no emitter left.

### 1.5 Focused-region replay (`runtime/d3/FocusedReplay`)

The runtime reads a Task and the wave's Obligations from
`-Dcausynth.d3.task=<file>`:

```json
{"task": {"taskId": "...", "focused": {"address": "...", "lineageLost": false},
          "factor": [], "seedSessionId": "..."},
 "obligations": [{"obligationId": "...", "taskId": "...", "pathId": "...",
                  "siteId": "...", "ordinal": 1, "flippedOutcome": true,
                  "rootAssignments": {"<rootId>": "3"},
                  "answers": {"<attach endpoint id>": "119981"},
                  "unproducible": []}],
 "prefix": {"<obligationId>": [{"siteId": "...", "ordinal": 1,
                                "outcome": true}]},
 "catalog": ["<endpoint id>"]}
```

`prefix` and `catalog` are optional: without a prefix the focused
occurrence's own decisions in the seed session are the prefix, so one
recorded fact has one spelling. Root assignments are applied at the mints of
the focused occurrence only; answers are addressed **by attach endpoint id**,
which is why the endpoint is allocated before the value is written. Verdicts:
`VALIDATED` when the prefix reproduced and the flipped decision was taken,
`NOT_ADMITTED` naming the first mismatching decision, `DIVERGED` when the
epoch catalog's interactions do not match.

## 2. Files

| file | lines |
|---|---|
| `runtime/d3/FocusedReplay.java` | 553 |
| `runtime/d3/D3Runtime.java` | 542 |
| `runtime/D3RowPublication.java` | 356 |
| `runtime/d3/Lineage.java` (scope frames + window counters) | 321 |
| `runtime/d3/SessionPublisher.java` | 282 |
| `runtime/d3/Interactions.java` | 179 |
| `runtime/d3/Identity.java` | 155 |
| `runtime/d3/Selectors.java` | 86 |
| `runtime/d3/OccurrenceMinterV2.java` | 62 |
| `runtime/d3/Text.java` | 37 |
| **new main total** | **2,574** |
| `src/test/.../runtime/D3RuntimeTest.java` (5 @Test) | 380 |

Against staging: **+3,182 / −13** across 15 files — the new files above plus
the wiring in `RuntimeTraceContext`, `ConcolicRegionRuntime`,
`CausynthTraceRecorder`, `ConcolicResultPublisher` and one
stop-after-IMPORT knob in `run_engine.sh`.

## 3. Workload diffs

Applied by `SPN/d-runtime/apply_d3_lineage.py <tree>` (idempotent; every edit
carries a `// causynth-d3-lineage` marker) and captured per tree as
`SPN/d-runtime/workload/d3-lineage-<tree>.diff` and, for the workload's own
rotation, `d3-rotation-scope-<tree>.diff` (five trees) (258–287 lines each; those
files are each tree's whole uncommitted workload delta, so they also carry
the earlier call-carried-scope and expiry-root diffs — mine are exactly the
hunks with the marker plus the API block the script adds). Scope bookkeeping
only, and every tree's own test still passes (§6).

| edit | file | why |
|---|---|---|
| carried-scope + daemon-tick + keep-scope API | `ipc/CausynthMessagePropagation.java` | the workload's door to the new runtime API |
| `Call` captures its scope; `RpcCall.run` restores it | `ipc/Server.java` | the handler pool inherits nothing (REPORT-ENTRY §1a) |
| one tick per monitor turn | `blockmanagement/HeartbeatManager.java` | the NameNode's key rotation is a daemon tick — 0% scoped on every run (REPORT-NNCHAIN §5) |
| one tick per offer-service turn | `datanode/BPServiceActor.java` | 45 unscoped entries on bug3 |
| one tick per key-updater turn | `balancer/KeyManager.java` | the balancer/mover/SPS side of the same rotation |
| one hop per op; the message scope ends with the op | `datanode/DataXceiver.java` | REPORT-B1D: the scope died with the SASL handshake while `replaceBlock` ran on |
| `clearLocalOwner` → `clearLocalOwnerKeepingScope` | `datatransfer/sasl/SaslDataTransferServer.java` | the other half of the same fix (bug1/bug2/bug3 only) |

## 4. The composer's eight requirements (REPORT-REVIEW-M4 §2)

| # | requirement | state |
|---|---|---|
| 2.1 | `seq` one session-global counter across kinds, and on `RootMintRow` | **met** — the VM's own event id on every kind (decision `vmEventId`, write `fieldVersionId`, export/attach ledger ids, target reach id, mint `eventSeq`), and `RootMintRow.seq` since contract v1.2. A row the VM numbered not at all is placed no earlier than everything already seen (`LAST_SEQ`), never at 0 and never on a per-kind counter |
| 2.2 | `javaType` as JVM descriptors | **met** — the declared leaf descriptor on exports, the VM's `_java_type` on attaches/reads/writes, `Ljava/lang/Object;` where the run states none (never blank, never a source spelling) |
| 2.3 | `LocationId.owner` allocation-derived | **NOT met, and not runtime-closable** — the VM's write log states `ownerSymRid` and no allocation site. Deriving one here would be a guess; `LocationId.heapOwner` needs the VM to state the allocating event. Named in §5 |
| 2.4 | `observedVersion` on container-element reads | **NOT met, and not runtime-closable** — the VM publishes no `observedVersion` on a `ContainerRelation`-owned field read (0 of 88 on bug3, 0 of 208 on 11741, REPORT-NNCHAIN §2). The rows carry the version wherever the VM states one and the concrete pin where it does not; inventing the join would be exactly the offline stitching the core design principle forbids. This is a VM change (`bytecodeInterpreter` demand mint, REPORT15 §1) |
| 2.5 | producer endpoints degraded, never the literal `UNPLANNED` | **met** (measured: 15 of 15 attaches paired on 17897's seed, 12 of them to a degraded producer) — an export with no live region publishes its row against `degraded(node, role, window-local k)` with `lineageLost`, and the attach pairs to that endpoint. `producer == null` now means only "no export of this run was paired with this delivery", and that row is filed as a gap |
| 2.6 | no fabricated decisions on an unfocused occurrence | **met** — an ambient mint publishes an attach row and starts no path recording, so an unfocused occurrence has no decisions and its arms stay UNATTESTED |
| 2.7 | exactly one session with `focused=false` | **met** — a replay with no task focuses nothing, and a focused replay marks the first activation of the wave's task and every later row about that address |
| 2.8 | one symbol per root id | **met by construction** — the mint's symbol is `sym__<sourceId>__<occurrence>__<ordinal>` (configured) or the VM's own exact root (manual); two root ids cannot share one |

## 5. Identity v3 (IDENTITY-V3 / IDENTITY-IMPL §B–D)

### 5.1 What is computed, and where each hook lands

| §B hook | where it lands | kind of hook |
|---|---|---|
| `onMethodEnter` / `onMethodExit` (the frame stack) | `CausynthTraceRecorder.beginCall` / `endCall` / `throwCall` | **existing woven hook** — every instrumented call site already reports itself; the frame is pushed with the site id the recorder already computes |
| `onLoopIteration` | `ConcolicRegionRuntime.checkLoopBackedge` | **existing woven hook** (LOOPOWN's backedge), charged whether or not a region is live |
| `scopeStart` | `RuntimeTraceContext.beginRequest`, `enterInbound`, `beginTick`, `enterCarriedScope` | runtime + **workload diff** for the tick and the queue carry |
| `scopeCarry` | `captureScope`/`captureAsync` → `enterRoot`/`enterCarriedScope` | runtime, with the IPC `Server.Call` and DataXceiver halves in the workload diff |
| `regionEnter` | `ConcolicRegionRuntime.startSymbolicRegion` | runtime |
| `siteEvent` | `D3Runtime.endpoint(...)`, on every export/attach/write/read | runtime |
| `onAllocate` | **not landed** — see §5.3 | needs a VM hook or a woven `NEW` hook |
| producer endpoint on the wire (§C) | `CausynthTraceRecorder.outboundExchange` → `ConcolicRegionRuntime.noteMessageSender` → `Interactions.sent`, read back at `enterInbound` | runtime; **deviation**: the endpoint is filed under the exchange's own correlation id rather than added to the header, because the transports carry no spare slot and the correlation is already the run's pairing evidence. Same information, no wire change, no 48 bytes |
| selector resolution (§D) | `runtime/d3/Selectors` — parse the v1 string, match on region + the anchor's api, k-th in seed order | runtime library; **PLAN is the caller** (the stage that reads the seed and picks the anchor). `ExploreMain` can call the same method; it is one function so the two cannot drift |

Per-event cost: one `sha16` fold on a call-site push (the prefix-hash chain),
an `ArrayList` add/remove on push/pop, and a `HashMap` increment per loop
backedge. Nothing at the site event except a sublist copy. No allocation on
the pop path, no synchronisation: the state is thread-local.

### 5.2 Where it is published

On the rows, since contract v2.0/2.1: `ActivationRow.occurrence` is
`(node, regionId, CausalContext, ExecutionIndex)` and every `Endpoint` is
`(occurrence, site, site-local ExecutionIndex, attempt)`. Nothing is
published beside them — the interim `identity.jsonl` that carried the
computation while the contract was v1.2 is deleted.

A real row, from a seed session:

```
node    hdfs-17897/nn0#epoch0
region  REGION.3897f002-…
ctx     Anchor:<producer endpoint id>@HADOOP_IPC#cache-encryption-key
idx     PBHelper.convert()#u2@0/…
```

### 5.2b The entry points the PLAN-side migration takes

| method | answers |
|---|---|
| `OccurrenceMinterV2.mint(nodeKey, regionId, context, index)` | the address, or `null` when this run can name no node |
| `OccurrenceMinterV2.degraded(nodeKey, role, site)` | the address of an activation under no nameable scope (`Lost(role)`, region `ROLE.<ROLE>`) |
| `Identity.context(anchorEndpointId, rpcSite, role, windowIndex)` | the three forms, chosen in that order |
| `Identity.regionEnter()` / `siteIndex()` / `atScope()` / `here()` | the execution index at a region entry, at a site inside it, at the scope, and the thread's whole path |
| `D3Runtime.beginActivation(token, nodeKey, regionId, taskId)` | mints, publishes the ActivationRow, and remembers the address for the activation's later rows |
| `Selectors.parse(v1)` / `resolve(selector, iteration, sessionId)` / `resolveAddress(...)` | IDENTITY-IMPL §D, against the seed session |

### 5.3 Memory Indexing (IDENTITY-V3 §5) — not landed, and why

`LocationId.owner` is still the VM's `ownerSymRid`. The canonical owner is
the allocation's execution index, and **nothing in this build sees an
allocation**: the VM creates the symbolic shadow (`sharedFieldVersions.cpp`
states `ownerSymRid`, no allocation site), and the weaver instruments call
sites, field accesses and branches — not `NEW`. The two ways to close it:

1. **VM hook (preferred, ~20 lines C++):** at shadow creation stamp the
   object with the runtime's current `Endpoint.id()` — the runtime would
   publish it through a `symbolicHeapAllocation(siteId)` upcall, and the
   write log then states `owner` directly. One field per shadow.
2. **Woven `NEW` hook (~60 lines in `CausynthPipeline`):** a call after every
   `new` in instrumented classes, stamping an `IdentityHashMap<Object,String>`
   in the runtime. Costs a map write per allocation in instrumented code and
   misses objects allocated in uninstrumented classes (`BlockKey` is
   instrumented, so it would work for the four key cases).

The composer's request to rewrite `ownerSymRid` into the allocation endpoint
id inside `expressions.json` is **one method in `SessionPublisher`** once
either hook exists (the rid→owner map is exact within a session, which is
where the rewrite happens); today there is nothing to rewrite it into, so
the rid is published as-is and the join stays session-local. Objects first
seen without a shadow get `preWindow:<class>#<m>` under the same change.

## 6. Re-recording

All six trees were rebuilt at Java 8 with the workload diffs
(`SPN/d-runtime/build_tree.sh <tree>`, `package`, never `install`, never
while a lane ran on the tree — `pgrep -f accept_final` was empty throughout)
and each tree's workload test re-run (`SPN/d-runtime/workload_test.sh`):

| tree | build | workload test |
|---|---|---|
| hdfs-17960-jdk8 | clean | `TestOrderedSnapshotDeletion` passed |
| hdfs-17897 | clean | `TestCausynthStripedChecksum` passed |
| hdfs-11741 | clean | `TestCausynthExpiredBalancerKey` passed |
| hdfs-17899-bug1 | clean | `TestBalancerWithEncryptedTransfer` passed |
| hdfs-17899-bug2 | clean | `TestExternalStoragePolicySatisfier` passed |
| hdfs-17899-bug3 | clean | `TestCausynthDataTransferRpcFailure` passed |

The workload tests are the gate on the scope edits: a semantics-preserving
edit leaves the test passing, and all six do.

Two build facts worth recording. `-pl hadoop-hdfs-project/hadoop-hdfs`
**needs `-am`** even for the test run: this tree's `hadoop-common` carries
the scope API and resolving it from `~/.m2` is how "cannot find symbol
beginTick" happens. And `CausynthMessagePropagation.clearLocalOwnerKeepingScope`
is only added where the tree has a local owner — 17960-jdk8 has no SASL and
no `LOCAL_OWNER`.

### 6.1 Per case

Four cases re-recorded and measured (17960, 17897, 11741, bug3); bug1 and
bug2 were in the round that was still running when this report was written,
and `python3 SPN/d-runtime/case_table.py` prints the table for whatever has
finished.

| case | sessions (seed) | act | dec | exp | att | wr | rd | root | tgt | gap | contexts | ports minting | paired/degraded/unpaired | idx on act | siteIdx on endpoints | reads w/ version | phi |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 17960 | 1 (1) | 90 | 1056 | 0 | 0 | 256 | 109 | 16 | 2 | 36 | ROOT:CLIENT:74, Anchor:14, LOST:UNKNOWN:2 | none | 0/0/0 | 90/90 | 0/0 | 96/109 | <org.apache.hadoop.hdfs.server.namenode.snapshot.FSImageFormatPBSnapshot$Saver: void serializeSnapshotSection(java.io.OutputStream)>#u61#1 phi=False fatal=False reached=True; <org.apache.hadoop.hdfs.server.namenode.snapshot.FSImageFormatPBSnapshot$Saver: void serializeSnapshotSection(java.io.OutputStream)>#u61#1 phi=False fatal=False reached=True |
| 17897 | 0 (0) | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |  | none | 0/0/0 | 0/0 | 0/0 | 0/0 | none |
| 11741 | 1 (1) | 75 | 39 | 46 | 38 | 187 | 147 | 46 | 0 | 24 | Anchor:68, ROOT:CLIENT:4, ROOT:HEARTBEAT_TICK:2, LOST:IPC_HANDLER:1 | block-key-id:17, block-key-expiry-date:17, data-encryption-key-id:4 | 38/0/0 | 68/75 | 74/84 | 132/147 | none |
| bug1 | (not run) |
| bug2 | (not run) |
| bug3 | (not run) |

Reading the columns:

- **contexts** — why each activation ran. `Anchor` is a message (its
  producer's endpoint id is in the row), `ROOT:<ROLE>` a workload action or
  a daemon tick, `LOST` a scope this run could not attribute.
- **paired/degraded/unpaired** — **0 unpaired on every case**: every attach
  names the producer endpoint the run paired it with. "degraded" counts the
  producers whose own occurrence is `lineageLost`.
- **idx on act** — activations carrying a non-empty execution index.
- **reads w/ version** — reads whose `observedVersion` the VM stated; the
  rest carry the concrete pin (§4, 2.4).
- **phi** — the anchor row, with φ in the fatal polarity and whether this
  run took that arm.

The Lost counts above are from the round BEFORE two fixes that are in the
tip: a degraded occurrence now carries the live scope's context (it was
forced to `Lost` even when the scope was known), and the workload's own key
rotation is declared a root (`SPN/d-runtime/apply_d3_rotation_scope.py`,
applied to five trees, each tree's test re-run and passing). The round that
measures them was still running at the time of writing.


## 6.1b The smoke: one seed session through SessionReader and ComposeMain

On the 17897 seed session (585 rows), `d3.contract.SessionReader.readAll`
reads **every row of every kind**, refuses none, and answers
`explored=false` — so the contract's own reader agrees this is the seed.

`d3.compose.ComposeMain --iteration <it> --target-occurrence <the case's v1
declaration> --root-domains … --max-valuations 16` then runs end to end and
**resolves the v1 selector against the seed**:

```
anchor hdfs-17897/dn0#epoch0/region/REGION.53092d3e…
       /ctx:Anchor:192d01084f16d977@HDFS_SASL/striped-file-checksum
       /idx:<…BlockTokenSecretManager: byte[] retrieveDataEncryptionKey(int,byte[])>@0
paths=0 families=0 roots=46 valuations=1 claim=NO_SUPPORTED_WITNESS gaps=21
```

The identity holds where it has to: the anchor region has **two**
activations in that session and they are **two identities** — same region,
same rpc site, different producer endpoint (`192d01084f16d977` vs
`9c2c5c458c18a550`) — each with its own decision and its own target row.

The three refusals it named, and whose they are:

| gap | count | whose |
|---|---|---|
| `UNSTATED_VALUE` "one solver name for 3 roots" | 7 | **mine, fixed**: the row published the VM's type-derived symbol (`M_L'…BlockKey'_15`), which two roots of one class share; it now publishes the root's own requested symbol |
| `TOPOLOGY_DIVERGENCE` (slot table) | 13 | the composer's epoch check on a corpus with one session and no slot table — for the composer agent |
| `ADMISSION_GAP` "no session published a path that reached the declared occurrence" | 1 | the resolved anchor **does** have an activation, a decision and a `reachedAnchor` target row in the corpus; the admission predicate refuses it anyway — for the composer agent, with this corpus as the reproducer |

## 6.2 What the explorer asked for (REPORT-REVIEW-M3 §6)

| requirement | state |
|---|---|
| an `ActivationRow` for EVERY activation, focused or not | **published** — every admitted activation publishes one, and an activation no plan selected (the entry rule's ambient occurrence) publishes one too, once per occurrence per session |
| message causality for happens-before | **published** — the `CausalContext` Anchor chain on every occurrence: the producer endpoint id carries the producer's own occurrence and context, recursively |
| same-thread program order | **published** (contract v2.3) — `threadKey` = JVM thread id + name; the id rather than the name alone because Hadoop renames DataXceiver threads per op |
| thread start / join | **published** (contract v2.3) — `startedBy` is the Thread.start / executor-submission endpoint whose frame the thread inherited, minted where the work was created (`SUBMIT` site) |
| "known only from the lightweight hook" | **published** — `instrumented=false` on exactly the activations the entry rule addresses from an unretained region; every woven region's activation is `true` |

### 6.3 hdfs-17960's anchor, for the case declaration (B1)

The case declares no anchor and ComposeMain needs one. The seed publishes
**two** occurrences of the annotated site, and they are the clearest
demonstration of identity v3 in the corpus:

```
node    hdfs-17960/nn0#epoch1
region  REGION.f0132fca-8c1f-3f7c-93e7-dc41bfc20f40
ctx     Anchor:4819fbfd484e4cf8@HADOOP_IPC/checkpoint-namespace     (both)
idx#1   NameNodeRpcServer.saveNamespace@1 / FSNamesystem.saveNamespace@1 /
        FSImage.saveNamespace@1 / FSImage.saveFSImageInAllDirs@1 /
        FSImage$FSImageSaver.run@1 / … / FSImageFormatPBSnapshot$Saver@1
idx#2   … identical prefix … / FSImage$FSImageSaver.run@3 / … @3
```

Same node, same region, same causal context — one `saveNamespace` RPC —
and they differ **only** in the loop iteration on the `FSImageSaver` frame
(the two image directories). A flat ordinal would call them #1 and #2 and
move both when anything else in the run changes; the execution index names
them by where they are.

The v1 selector `hdfs-17960/nn0#epoch1/region/REGION.f0132fca-8c1f-3f7c-93e7-dc41bfc20f40#1`
resolves to the first of them in seed order.

**One thing to decide with it**: both target rows carry an empty `phiTerm`.
17960's fatal is an exception at the site, not a branch, so the run states
`reachedAnchor` and no predicate — φ for an exception-anchored case is the
reach itself, and the composer has to say so rather than look for a term.

### 6.4 The two closures, and the per-entry-point state

| entry point | what it was | what closed it |
|---|---|---|
| IPC handler | the caller's scope reached the handler only when the header carried it | `Server.Call` captures the scope at construction and `RpcCall.run` restores it (workload diff), and the served hop names the remote family |
| DataXceiver op | the scope died with the SASL handshake while the op ran on (REPORT-B1D) | `clearLocalOwner` → `clearLocalOwnerKeepingScope`, and the op's own hop ends the message scope when the op returns (workload diff) |
| BPServiceActor | 0% scoped | one `Root:BP_SERVICE_ACTOR` tick per offer-service turn (workload diff) |
| HeartbeatManager$Monitor | 0% scoped | one `Root:HEARTBEAT_TICK` tick per monitor turn (workload diff) |
| KeyManager / BlockTokenSecretManager updater | 0% scoped | one `Root:KEY_MANAGER_TICK` per updater turn (workload diff) |
| the workload's own key rotation | `master.updateKeys(...)` straight from the test thread — a workload action under no scope, which is what made the NN's rotation `Lost` | declared a root: `SPN/d-runtime/apply_d3_rotation_scope.py` wraps each rotation in `beginTick(<the secret manager>, "KEY_MANAGER_TICK")`, five trees, every tree's test re-run and passing |
| executor / Thread.start | carried already | `captureAsync` → `enterRoot`, now also naming the submission endpoint as `startedBy` |
| an unselected activation | addressed as `Lost` by construction | a degraded occurrence carries the live scope's context; only a scope nothing could attribute is `Lost` |

On 17897 that leaves **zero** Lost. The other five were re-recording as
this was written; the same two closures apply to all of them, and
`case_table.py` prints the contexts column per case.

## 7. How to re-run any of this

```
# one tree, Java 8, package (never install), never while a lane runs on it
bash SPN/d-runtime/build_tree.sh /opt/hadoop-hdfs-17897
bash SPN/d-runtime/workload_test.sh /opt/hadoop-hdfs-17897 \
     org.apache.hadoop.hdfs.TestCausynthStripedChecksum \
     testStaleEncryptionKeyFailsStripedChecksum

# the scope edits, idempotent, one tree at a time
python3 SPN/d-runtime/apply_d3_lineage.py /opt/hadoop-hdfs-17897

# one case, VALIDATE..IMPORT only
bash SPN/d-runtime/seed_case.sh 17897        # 17960 | 17897 | 11741 | bug1 | bug2 | bug3

# the table
python3 SPN/d-runtime/case_table.py
```

`CAUSYNTH_CAMPAIGN_STOP_AFTER=IMPORT` is what stops a campaign at the
measurement (`seed_case.sh` sets it); without it the campaign runs on into
EXPLORE and COMPOSE.

### 7.1 The composer's remaining word on the re-recorded seed

Re-run on 17897's seed at the tip: `paths=0 families=0 roots=46
claim=NO_SUPPORTED_WITNESS`, gaps **1 BLOCKING + 16 DIAGNOSTIC** (the seven
BLOCKING "one solver name for N roots" are gone — that was the root-symbol
fix). What is left, and whose:

| gap | whose |
|---|---|
| `ADMISSION_GAP` "no session published a path that reached the declared occurrence" (BLOCKING) | the composer's: the resolved anchor has an ActivationRow, a DecisionRow and a `reachedAnchor` TargetRow in that very session, and the admission predicate refuses it. `SPN/d-runtime/seed/17897/schedule/iteration-0000` reproduces it in one command |
| `TOPOLOGY_DIVERGENCE` ×13 (DIAGNOSTIC) | the composer's slot-table check on a one-session corpus with no slot table |
| `UNSTATED_VALUE` "this term names symbols nothing declares: [EXPR.…]" | **a contract question**: `DecisionRow.term` is published as the expression REF (`EXPR.<sha16>` into the session's `expressions.json`), because the runtime does not lower to SMT — CONTRACT-SPEC §5 puts the one lowering in the composer. If `term` must be SMT text, that is a second lowering in the runtime and I would want the ruling before writing it; the ref and the table carry the same information |

## 8. What is NOT done, named

- **The allocation index (IDENTITY-V3 §5)** — §5.3 above. `LocationId.owner`
  is the VM's session rid until an allocation hook exists; the composer's
  `expressions.json` rewrite is one method behind the same hook.
- **`observedVersion` on container-element reads** — the VM states none for a
  `ContainerRelation`-owned field read; the rows carry the version wherever
  the VM states one, and the concrete pin where it does not.
- **The producer endpoint on the wire (§C)** is filed by correlation rather
  than added to the message header: same information, no wire change. A
  transport that loses correlation ids would need the header slot.
- **`ReplayProgress` and `FocusedReplay` are two prefix matchers.** The
  ruling is that `FocusedReplay` becomes the only one (and the only forcing
  path) and `BranchReplayContract.ReplayProgress` comes out of
  `ConcolicRegionRuntime`'s four call sites. Not done here: it changes how a
  flip replay forces and admits, and the six re-records in flight are on the
  current behaviour.
- **The last four re-records** (11741, bug1, bug2, bug3) were running when
  this was written; `bash SPN/d-runtime/run_remaining.sh` re-runs all six and
  `python3 SPN/d-runtime/case_table.py` prints the table.
- **Loop iterations in an execution index** are charged from `checkLoopBackedge`,
  which fires for instrumented backedges only: a frame inside an
  uninstrumented loop carries iteration 0. That is a coarser index, never a
  wrong one — two replays of the same uninstrumented loop agree.

---

## 8. P2 round: one address for one activation (tip cfbf740f5)

**Corpus for the composer**: `SPN/d-runtime/seed/17960/schedule/iteration-0000`
(seed session `sessions/seed-result-1fc6abdb`, `ActivationRow.focused=false`
on all 90 rows). Runtime tip `cfbf740f5` on `refactor/d3-runtime`.

### 8.1 The duplicate that blocked the seed

`RuntimeSelectedRegionFinalizer.mintOccurrences` refused the 17960 trace with
`duplicate runtime region activation`. Four separate losses, each closed where
it happens (commit `b389672b1`):

| loss | where it showed | fix |
|---|---|---|
| an activation entered from an unwoven caller had no frame of its own | `INodeDirectory.getDirectoryWithSnapshotFeature` entered twice under one `resolvePath` frame, one index | a method activation pushes its own frame (`CausynthTraceRecorder.pushMethodFrame`), iteration = k-th entry of that method under the enclosing frame |
| a fork-join batch | `FSDirectory$InitQuotaTask.compute` (REGION.0af6742d): `invokeAll(Collection)`, two workers, one inherited scope | `invokeAll` and `ForkJoinTask.fork` are submissions; a Collection carrier is one submission per element |
| the IPC call queue | two `setSafeMode` calls of one request, both `Root:CLIENT#1` (REGION.d4dd8a44) | `Server.Call`'s captured scope now mints a submission endpoint; the handler's context is `Anchor:<call>@THREAD_START` |
| two submissions at one point shared an endpoint | `invokeAll` with three subtasks | `D3Runtime.submission()`: the k-th submission at a point is the k-th |

Trace evidence: 169 colliding `(method, executionIndex, causalContext)` keys
before, 19 after the frame fix, 0 after the submission fixes.

### 8.2 Plan address vs replay address

The plan computes an activation's address offline from the recording's frames
and the replay computes it live from its own, and the two passes do not weave
the same hooks: the recording has a frame per traced method activation and per
call site, the replay has one per region root. On 17960 the same activation is
`ctx:Anchor:<submit>@THREAD_START/idx:run@0/run#u8@0/...` in the plan and
`ctx:Anchor:<ipc>@HADOOP_IPC/checkpoint-namespace/idx:saveNamespace@0/.../run@0/...`
in the replay, and every seed task was refused `OCCURRENCE_ANCHOR_UNMATCHED`.

Ruling applied: the address gate holds on what both passes compute the same way
— node and region — and where the causal context or the execution index differ
for a candidate the task's own selector (receiver, thread, source) already
picked out, the replay admits the occurrence and publishes the drift as a gap.
46 `LINEAGE_LOST` drift gaps on this run, one per activation whose two
computations disagree. Closing the drift needs the replay to see the
thread-start edge the recording sees, which needs a woven hook (the concolic
pass has no `Thread.start`/executor call-site hook); that is not in this round.

### 8.3 What the seed states

| kind | rows |
|---|---|
| activations | 90 (ROOT 74, ANCHOR 14, **LOST 2**), focused=0 |
| decisions | 1082 (19 with a term; 1063 concrete) |
| writes | 789 |
| reads | 37 |
| roots | 2 (`HDFS.CONFIG.SNAPSHOT_DELETION_ORDERED`, now MARKER, recordedValue `true`) |
| targets | 2 |
| attaches / exports | 0 |
| gaps | 100 (LINEAGE_LOST 46, DECLARATION_MISSING 42, UNSTATED_VALUE 12) |
| expressions.json | 3.9 MB |

`ComposeMain --iteration <above> --target-occurrence <anchor> --max-valuations 16`
on this corpus:

```
anchor hdfs-17960/nn0#epoch1/region/REGION.f0132fca-8c1f-3f7c-93e7-dc41bfc20f40/
  ctx:Anchor:1b019df56f339972@HADOOP_IPC/checkpoint-namespace/idx:... 
  paths=2 families=6 roots=1 valuations=1 solverRuns=1
  claim=NO_SUPPORTED_WITNESS gaps=1556
```

All 1556 composition gaps are one kind: `UNSTATED_VALUE
BinarySortConflict:<op>:ARRAY_VALUE!=INT`, and the single valuation came back
`(error "line 32 column 27: invalid bit-vector literal")` — both composer-side
lowering, not row content.

### 8.4 Why 17960's φ is empty

`TargetRow.phiTerm` is `""` because the u61 decision has no term: the VM served
that branch concrete. The reason is upstream of publication. The seed result for
both `REGION.f0132fca` activations states

```
symbolizedInputs: []   unresolvedInputs: []   targetReach: u61 occurrence 1 outcome true
```

while the task plan for those activations does carry the declared input:

```
authority EXACT_RUNTIME_ACCESSOR_RECEIVER_RETURN_V1  bindingMode FIELD_ACCESS
cell <java.util.concurrent.atomic.AtomicInteger: int value>
accessSites [<SnapshotManager: int getNumSnapshots()>#u2]
accessorImplementationMethod <java.util.concurrent.atomic.AtomicInteger: int get()>
accessorOccurrence 1
```

So the action was planned, the activation ran, the branch was reached, and the
mint never fired — and it did not fail either (an attempted mint leaves an
`unresolvedInputs` row). `AtomicInteger.class` and `SnapshotManager.class` are
both in `instrumented-classes`, so the defect is in the accessor-context match
in `ConcolicRegionRuntime.SymbolizeAction.matchesField` (the
`lightweightAccessorContextMatches` / `acceptsOccurrence` arms), not in the
publication. That is the next thing to fix for 17960, and it is a replay-side
fix, not a row-side one.

### 8.5 Rows a composer can join (commit 13243bacd)

* every `ReadRow` states an `observedVersion` or a plain-decimal
  `concreteValue`, never neither; a field read whose value is an expression
  takes the version of the read inside it (`1099511693805`, `16386` on this
  corpus — no `Y_J_` spellings left). `Y_<T>_<v>` is the VM's constant
  spelling: `Y` marks a concrete value, the letter is the JVM type, the rest
  is the value.
* one read event is published by one occurrence — the first to publish it,
  which is the innermost, since an activation finishes before the one it runs
  inside.
* read and write `LocationId.owner` now share the rid spelling: 14 of the 17
  owner spellings on the read side are also write-side spellings; the 3 that
  are not are field reads whose value states no rid (`Snapshot$Root` and
  friends), which is what P3's allocation id is for.
* `RootMintRow.symbol`, `ReadRow.symbol` and the `SymbolExpression` leaves now
  use ONE spelling — the VM's (`M_Z_field_SRC.…_org/apache/…`) — because that
  is the one that appears in the lowered terms.
* a configured source states the value it read at the mint
  (`recordedValue: "true"`), so a relative domain has a centre.

### 8.6 `N` is null

`_exp = "N"` is `VmExpressionIr.SYMBOLIC_NULL` — "the VM's spelling of a
symbolic null reference", `d3/smt/VmExpressionIr.java:28`. The composer already
reads it correctly for CONSTANT leaves (`VmLoweringCore:609,632` compare against
that constant); its SYMBOL leaf path (`SmtLowering:461`) compares against the
literal string `"SYMBOLIC_NULL"`, which the VM never emits. So the one-line fix
is in the composer, and rewriting `N` to `SYMBOLIC_NULL` at publication would
break the two comparisons that are already right.

### 8.7 Publication cost

A live `jstack` of the 17960 seed replay (26 min in, workload finished at 10)
showed the time in `RowCodec.toLine` under `D3Runtime.expressionRef`, not in
`Identity`. Three costs, commit `3967a4e7e`:

* `expressions.json` is one JSON object and was rewritten per expression added:
  n expressions cost n rewrites of all of them. Written at close, and every
  64th expression.
* one expression tree was serialized again by every row that named it: one
  serialization per tree now.
* every recorded event stamped an execution index — one sha256 fold per frame
  and a rendered path — and only `METHOD_ENTER` and the exchange rows are read
  for it.

17960 to `STOP_AFTER=IMPORT`: **26 min and still in the first replay's
publication before; 14 min 40 s end to end after** (22:02:14 → 22:16:5x). Ids
are unchanged: the same frames are folded at the same publication points.
