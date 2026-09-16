# REPORT-ENTRY — the entry rule: every declared port mints, selection decides only COMPOSE

Design only. No branch, no code. Companion to `IDENTITY-V2.md` §2; the
measurement in §1 below is the one IDENTITY-V2 phase 1 names as its gate, and
it is available today from recordings already on disk.

---

## 0. The headline: half of this is already built

`stageMessageExpression` (`ConcolicRegionRuntime:2033-2050`) **already
implements the entry rule on the OUT side**:

```java
String producerTask = active == null ? UNPLANNED_ENDPOINT
        : active.activation.taskId;
String producerOccurrence = active == null ? UNPLANNED_ENDPOINT
        : active.occurrenceId();
// The producer site ran, so the message carries the value.  Which
// occurrence produced it and which the plan addressed are what the
// entry says about itself, not conditions on saying it.
```

An export with no live region stages the value anyway and says `UNPLANNED` of
itself. **The IN side does the opposite**: `mintArrivedCommunicationLeaf` and
`recordVmHandoffEvent` both begin `ActiveRegion active =
attachConsumerRegion(site); if (active == null) { … return; }` — one raises
`RPC_HANDOFF_NO_ACTIVE_REGION`, the other returns silently.

So the entry rule is not a new mechanism. It is **giving the IN side the
sentence the OUT side already speaks**, and the whole of §3–§6 below is about
what an unselected consumer needs that an unselected producer does not: an
address, a k, and a place to put the row.

## 1. What the runtime already knows about scope loss

Measured now, from `METHOD_ENTER` rows in recordings on disk — every one
carries `threadName`, `requestKey`, `requestApi` and `source`, so "did this
activation have a request scope" is already a fact of the corpus.

| recording | METHOD_ENTER | with a request scope |
|---|---|---|
| hdfs-17960 (laneBR) | 1,688 | **1,677 (99.3%)** |
| hdfs-17897 (lane17897h) | 146 | 117 (80.1%) |
| hdfs-17899-bug3 (laneVM25) | 298 | **192 (64.4%)** |

Per thread family, bug3:

| thread family | scoped | unscoped | |
|---|---|---|---|
| `main` | 91 | 5 | 94.8% |
| `IPC Server handler` | 60 | **22** | 73.2% |
| `BPServiceActor` (`BP-…`) | 0 | **45** | **0%** |
| `HeartbeatManager$Monitor` | 0 | **26** | **0%** |
| `ThreadPoolExecutor` worker | 25 | 0 | 100% |
| `DataXceiver` | 16 | 8 | 66.7% |

### The two losses, named

**(a) The IPC `Server.Call` queue — observed, not predicted.** On bug3,
`BlockTokenSecretManager.updateKeys` runs on three handler threads of one
pool:

```
4  scoped=true   IPC Server handler 9 on default port 38093
4  scoped=true   IPC Server handler 5 on default port 38093
4  scoped=false  IPC Server handler 2 on default port 38093
```

Same method, same pool, same port — two handlers carry the caller's scope and
one does not. That is exactly the `InheritableThreadLocal` accident
`RuntimeTraceContext:259` documents for the Client sender pool, now seen on the
server side: a handler thread inherits a scope only if it was *created* inside
one, and the `Server.Call` queue carries no scope across the enqueue/dequeue.
**IDENTITY-V2 §1's "attach at enqueue, restore at dequeue" is required, and
this is its evidence.**

**(b) Timer/daemon roots — total.** `HeartbeatManager$Monitor` (10 of the
`updateKeys`/`BlockKey.<init>` entries), `BPServiceActor` (45 entries) and the
DN key-refresh tick carry **no** request scope at all, by construction: no
request created them. These are IDENTITY-V2's "daemon ticks", and they need a
root of their own, not a repair.

### Why this matters for the expiry root specifically

The unscoped bug3 entries are not incidental — they are the expiry root's own
sites:

```
12  DelegationKey.<init>                 unscoped
 6  BlockKey.<init>                      unscoped
 4  BlockTokenSecretManager.updateKeys   unscoped
 2  BlockTokenSecretManager.removeExpiredKeys
 2  BlockTokenSecretManager.setSerialNo
```

On 17897 the same five run unscoped on `main`. **The NameNode's key rotation
is a daemon tick on every case**, which is why REPORT-VM25 found the expiry
mint landing in an `updateKeys()` occurrence the composition does not consume:
there are two regions for one method because there are two scopes for one
method, and only one of them is a request the plan can address.

## 2. The rule

> Every declared communication port **mints on export and on attach whatever
> is selected**. The row states the occurrence it ran in, from the execution
> context. Selection decides only whether that occurrence's paths are
> explored and whether its rows enter COMPOSE.

What it deletes: `RpcExpressionHandoff.NO_ACTIVE_REGION` (the status, its
`reason()` arm, the emitter and the gap it raises) — 228 rows on lane17897h,
0 after. `MISSING_METADATA`'s "no task of this replay's slice declares this
capture's port" stays, and becomes rare rather than routine.

What it does **not** change: the handoff identity
`H = (portId, consumer address, k-th attach, element path)`, the phase-id
derivation, the VM label, the family join, or the address format.

## 3. Sites

| # | site | today | after |
|---|---|---|---|
| 1 | `exportCommunicationLeaf:2149` → `stageMessageExpression:2033` | already unconditional, says `UNPLANNED` | **unchanged** — except that `producerOccurrence` becomes the §4 address instead of the literal `UNPLANNED`, so the family arm has a producer to name |
| 2 | `attachCommunicationLeaf:2186` | needs a site from `communicationHandoffSite`, which already falls back to the whole plan's task list — a port declared anywhere resolves | unchanged |
| 3 | `mintArrivedCommunicationLeaf:2375` | `attachConsumerRegion(site) == null` → `NO_ACTIVE_REGION` gap, return | mints on the §4 ambient activation |
| 4 | `recordVmHandoffEvent:2299` | `attachConsumerRegion(site) == null` → silent return | files the event on the ambient activation |
| 5 | `declaredConsumerOccurrence:2634` | walks live regions, else the carrier's own occurrence | walks live regions, else **the §4 address** instead of borrowing the carrier's |
| 6 | `mintHandoffVariable:2500+` / `mintHandoffLeaf` | take `ActiveRegion active` | take a narrow interface both an `ActiveRegion` and the ambient activation implement |

Site 6 is the only signature change, and it is the one design decision worth
stating: **do not widen `ActiveRegion`.** Extract the four things the mint
actually uses from it —

```
long   nextHandoffAttach(String key)                 // k
ModelAssignment configuredSourceAssignment(...)      // the answer, or null
ExpressionStore expressionStore()                    // for compaction
void   recordVmHandoffEvent(JsonObject) / recordHandoffGap(JsonObject)
```

— into a `HandoffSink` interface. `ActiveRegion` implements it as it stands.
`AmbientActivation` implements it with a counter map, a `null` assignment
(nothing planned it, so nothing answers it), its own store, and a flush.
`ensurePathRecordingStarted(active)` is **not** on the interface: an
unselected activation must not start path recording — that is precisely what
not selecting it means.

## 4. The address of an unselected activation

Today `OccurrenceAddress.of(sourceKey, regionId, requestFamily, ordinal)`
refuses an empty `regionId`, and an unselected activation has no plan region.
It has everything else:

- **node**: `RuntimeTraceContext.current().source` — registered per node at
  `registerSource`, present on daemon threads (they are the node's own
  threads) even with no request;
- **family**: `OccurrenceAddress.familyOf(view.requestKey)`, which already
  renders `""` when there is no request — no new case;
- **k**: a counter.

So the only missing component is the region slot, and the design fills it with
a **role id** rather than a new address format:

```
regionId = "ROLE." + UUID.nameUUIDFromBytes(roleKind + "\n" + definitionMethod)
```

`roleKind` is the scope kind IDENTITY-V2 §1 defines (`IPC_HANDLER`,
`DATAXCEIVER_OP`, `BPSERVICEACTOR_TICK`, `KEYMANAGER_TICK`, `EXECUTOR_TASK`,
`WORKLOAD_ACTION`), derived from the thread's scope frame, **never from the
thread name** — the name is how I measured §1, not how the runtime should
decide. `definitionMethod` is the port's declared consumer method, which the
catalog already carries on `CommunicationHandoffSpec`.

Two properties make this cheap:

1. **No parser changes anywhere.** `OccurrenceAddress.parse` looks for
   `/region/` and a trailing `#k`; `ROLE.…` sits in the same slot as
   `REGION.…` and every reader keeps working. `render()` is unchanged, so
   `HandoffPhaseContract.phaseId(port, address.render(), k, elementPath)` is
   **unchanged** — the phase-id derivation needs no edit at all.
2. **`ROLE.` is a visible prefix**, so any reader that must distinguish a
   planned occurrence from an ambient one does it by `startsWith`, not by a
   new field.

**k**: per `(sourceKey, roleId, family)`, counted in a replay-window-local map
held beside `CURRENT_TOKENS`. Where a request family exists, k is the k-th
activation of that role inside that family — stable across runs. Where none
does (the daemon case), k is a raw window ordinal, which IDENTITY-V2 §0 already
rules acceptable *because the closure makes it harmless*: a daemon delivery the
anchor never reads is outside the closure, and one it does read is identified
by the version it wrote.

**Fail-closed**: if the node is unknown, the address is `OccurrenceAddress.NONE`
and the row publishes `lineageLost=true` with the port and element path, and
stays BLOCKING. Never a guessed address.

## 5. The row, and where it lands

`ConcolicResultPublisher.appendResult` already writes non-region rows to
`concolic_region_results.jsonl` — `CONCOLIC_REGION_SKIPPED` is the precedent.
The ambient row is a third kind on the same file:

```json
{"event": "CONCOLIC_AMBIENT_HANDOFF", "schemaVersion": 1,
 "taskId": "",                                  // no task: that is the point
 "occurrenceId": "<node>#epoch0/region/ROLE.<uuid>[@<family>]#<k>",
 "roleKind": "KEYMANAGER_TICK", "lineageLost": false,
 "topologyEpoch": "iteration-0000",
 "vmHandoffEvents": [ <exactly one, the existing VmHandoffEvidence shape> ],
 "sharedExpressionTable": { … },                // only the arms this row needs
 "rpcHandoffGaps": [ … ]}
```

**One row per attach, flushed immediately.** An `ActiveRegion` publishes at
region exit; an ambient activation has no exit hook and inventing one is the
expensive half of this change. Flushing per attach needs no lifecycle at all,
and the volume is known: the ambient rows are exactly today's
`NO_ACTIVE_REGION` attaches — **228 on lane17897h, 0 on laneVM25** (bug3
raised none; its 125 attaches all landed on selected activations, as did
17897's 85). So this is one extra line per delivery on a case that has the
problem and nothing at all on a case that does not.

`writeSkipped`'s shape is the model: build the object, `appendResult`, done.
**Estimated 25 lines in `ConcolicResultPublisher`.**

The importer's dispatch is one line —
`ConcolicSummaryImporter:569` already gates on
`"CONCOLIC_REGION_RESULT".equals(event)` and skips everything else, so ambient
rows are ignored by every existing path until a new collector reads them.

## 6. What the composer needs

The consumer side is the real work, and it is **not in my files**.

`PathMergeComposer` builds handoff families from `vmHandoffEvents` carried on
**admitted path summaries**. An ambient row belongs to no path, so today it is
invisible to `handoffFamilies(...)`. What it needs:

1. The importer publishes an `ambientHandoffs` array beside the summaries,
   **indexed by `handoffPhaseId`** — one entry per `(phase, port)` with the
   producer/consumer occurrence, the recorded value and the expression. ~60
   lines in `ConcolicSummaryImporter`, in my files.
2. The composer, when an admitted path's formula names a `v_H` whose phase has
   no arm among the summaries, takes the arm from `ambientHandoffs`. That is
   the **only** composer change: the family join itself is unchanged, because
   an arm is `(phase, port, side, expression)` and does not care whether its
   occurrence was a task. ~40 lines, `PathMergeComposer` — the concolic
   agent's.
3. `ROOT_NOT_ON_ANY_PATH` and `HANDOFF_CONTROL_ROW_ABSENT` keep their meaning
   and get quieter: an arm that exists ambiently stops being absent.

A useful consequence for GAPJOIN: with ambient rows present, the
`PORT_NEVER_ATTACHED` arm of `portVerdict` becomes the *only* way an
`RPC_HANDOFF_GAP` blocks, and `NO_ACTIVE_REGION` stops existing — the join
stays correct and its diagnostic arm stops firing, which is the right way for
a conditional class to retire.

## 7. Size

| file | ± | mine |
|---|---|---|
| `runtime/ConcolicRegionRuntime` — `AmbientActivation`, `HandoffSink`, address minting, sites 3/4/5 | +150 −20 | yes |
| `runtime/RuntimeTraceContext` — scope role + window-local k | +40 | yes |
| `contract/OccurrenceAddress` — `ROLE.` minting helper and `isAmbient()` | +18 | yes |
| `runtime/ConcolicResultPublisher` — the ambient row | +25 | yes |
| `concolic/ConcolicSummaryImporter` — collect and index ambient rows | +60 | yes |
| `concolic/RpcExpressionHandoff` + `contract/GapLedger` — delete `NO_ACTIVE_REGION` | −25 | yes |
| `concolic/PathMergeComposer` — family arm from an ambient row | +40 | **no** |

**≈ +293 / −45, of which 40 lines are the concolic agent's.** The runtime half
is self-contained and testable without the composer half: ambient rows can
land and be ignored for a whole lane before anything consumes them, which is
the order I would take it in.

## 8. Tests, folded, no new `@Test`

| existing test | assertion added |
|---|---|
| `runtime/HandoffMintTest` (5) | an attach with no live region mints, publishes one `CONCOLIC_AMBIENT_HANDOFF` row with a `ROLE.` occurrence and a phase id, and raises no gap; the same attach twice gets k=1 then k=2 |
| `runtime/OccurrenceAddressIsNotARequestTest` (5) | a `ROLE.` address round-trips through `parse`/`render` and `matches` exactly as a `REGION.` one; an ambient address with no node is `NONE` and the row says `lineageLost` |
| `concolic/HandoffBelongsToItsConsumerTest` (3) | a v_H whose consumer occurrence is ambient still belongs to that occurrence and not to the carrier's |
| `contract/GapLedgerTest` (2) | `RPC_HANDOFF_GAP` keeps its composed-port scope with `NO_ACTIVE_REGION` gone (the code retires, the class does not) |

Count stays 61.

## 9. Risks, and one thing to fix first

- **The daemon k is a raw ordinal.** Mitigated by IDENTITY-V2 §3's closure, not
  by this change. Until the closure lands, a daemon-rooted v_H is only as
  stable as the tick count, and two replays of one recording can disagree.
  This is the reason to land §1's rows before §2's addresses.
- **`ROLE.` ids are catalog-derived**, so a port whose declared consumer
  method changes gets a new role id. That is correct (it is a different site)
  but it means role ids are not comparable across plan revisions.
- **`IPC Server handler` scope is repairable and should be repaired first.**
  22 of bug3's 106 unscoped entries are handler threads that *should* have a
  request scope; fixing the `Server.Call` enqueue/dequeue carry turns them
  into ordinary request-family addresses and shrinks the ambient case to the
  genuine daemon roots. Doing the carry before the entry rule means fewer
  ambient rows and a smaller ambient surface to get right.
- **Dead code to remove while in there**: `ConcolicRegionRuntime:2051-2056`
  is an empty `try { } finally { }` left by MECHANISMS §9 when
  `observeOutgoingSourceAnchor` was deleted. It is mine and it is four lines;
  I did not touch it in the GAPJOIN commit because it was out of scope.

## 10. Order I would take it

1. The IPC `Server.Call` scope carry (§9) — smallest, and it shrinks
   everything downstream. Measurable with the §1 query, which needs no code.
2. IDENTITY-V2 §1 rows: role + lineage on every activation, no consumer
   change, gated on the §1 share per entry point.
3. This report's runtime half (§3–§5): ambient rows land, nothing reads them,
   `NO_ACTIVE_REGION` retires.
4. The composer half (§6) with the concolic agent.
