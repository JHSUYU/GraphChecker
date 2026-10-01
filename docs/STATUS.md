# Status

This page describes what the code on `main` (HEAD) does, measured against the owner's
requirements R1–R6. Every commit that completes or changes something listed here updates this
page in the same commit.

- **Done** means the code does it on HEAD.
- **Partial** means the code does part of it; the "missing" column says which part.
- **Not done** means the code does not do it, including work that is in progress.

Pointers are `path` plus class and method. `gc/` stands for
`src/main/java/edu/uva/liftlab/graphchecker/`, and `VM/` for
`third_party/OpenJDK-Concolic-Execution-Engine/hotspot/src/share/vm/`.

## Acceptance

Live runs on the concolic VM `/bigtemp/vnr3ne/vm-r3b/j2sdk-image`, outputs under
`/bigtemp/vnr3ne/gc-out/accept-<round>-<case>/`. Round `i1` ran this code (integration `int1`,
`d60d89cde`: the clock batch, the 11741 handoff fixes, the time robustness package, ADHOC-INFRA
WP5.B/5.D/WP3) on nine HDFS cases and SOLR-18406; SOLR-18413 last ran in `r9` and `w4d1`.

| case | run | verdict | mechanism / blocker |
| --- | --- | --- | --- |
| hdfs-17897 | `i1` | PASS | MARKER_FLIPPED, IPC request door (`REGION.763d087e`) |
| hdfs-17899-bug1, bug3 | `i1` | PASS | MARKER_FLIPPED, IPC request door |
| hdfs-17899-bug2 | `i1` | PASS | MARKER_FLIPPED, IPC response door (`REGION.9ffdee3d`) |
| hdfs-17960 | `i1` | PASS | MARKER_FLIPPED, `HDFS.CONFIG.SNAPSHOT_DELETION_ORDERED=false`, confirmed |
| hdfs-17967-pathA, B, C | `i1` | PASS | MARKER_FLIPPED, IPC request door |
| hdfs-11741 | `i1` | FAIL | NO_SUPPORTED_WITNESS: all 157 composed paths are unsatisfiable with every root free (BLOCKING). An arm now binds every handoff it names, which took away the earlier CLOCK_SKEW that rested on unbound handoff values; the workload rotates the cached key inside the recording window (`gc/hdfs-11741` `5cff0e12b1f`); the remaining contradiction is under investigation. |
| solr-18406 | `i1` | PASS | CLOCK_SKEW, one jump of the `IndexCommitWrapper.delete()` clock read in `IndexFileDeleter.checkpoint` past the commit's one-hour reservation (`reserves`), so generation 2 is deleted and `getAndSaveCommitPoint(2)` throws; confirmed, moved root in the cone. |
| solr-18413 | `r9` | FAIL | the `isExpired#u6` flip is SAT and its replay reproduces the fatal ("Could not find collection") and is ADMITTED, but IMPORT invariant 9 stops the campaign: that replay's target row states no `phiTerm`, since the fatal condition is concrete there. Fixed off main together with the VM's LinkedHashMap iteration order (open defect 29). |

So HDFS stands at 8 of 9 and Solr at 1 of 2 on main.

hdfs-11741 fails the cone gate (`experiments/accept/cone.py`): the NameNode clock roots it
moves lie outside the selected path's causal cone. In that formula, the DataNode's expiry
comparison is against recorded constants. No clock value crosses the process into it as data,
so R2's 11741 chain (the NameNode clock reaching the DataNode check) is not in the formula.

Rounds r3 (VM f13), r4 and r8 (VM R3; r8 on main 8820c3129) ended hdfs-11741
`INCONCLUSIVE_PARTIAL` on engine defects the richer recordings exposed, fixed on HEAD (r8 reached
`CLOCK_SKEW` and was blocked by the first three):

- PLAN `OCCURRENCE_ADDRESS_SHARED` (3 in each round): a pool's worker inherits no frames
  (`gc/runtime/PoolWorkers`), so the balancer's two move tasks, each submitted from the one site of
  an `executePendingMove` call, shared one address, and so did the two DataNode SASL handlers they
  reached, the anchor among them. A task now stands on the frames it was submitted under
  (`gc/runtime/Identity#startWork`). The address is recorded, so only a new recording shows it: two
  on it (`/bigtemp/vnr3ne/gc-out/accept-agent-a0f-id1`, `accept-agent-a0f-full2`) plan no shared
  address.
- EXPLORE `TOPOLOGY_DIVERGENCE` (32 in r3, 36 in r4, 18 in r8's last wave): the order check ranked
  two events by the anchor chain, so the dispatcher's later `isDelayActive` reads came before the
  move task's `activateDelay` writes they observed. It reads the rows' seqs (`gc/explore/SlotTable`).
- COMPOSE `UNSTATED_VALUE` (r4, r8): the second move task's export, sharing the first's endpoint
  and stating no expression, was read as a missing table entry (`ComposedFamilies#lower`).
- COMPOSE `UNPRODUCIBLE_ANSWER` (every SASL path in r3 and r4, 11 of 17 in r8): Independence walked
  a field projection's owner chain, which no lowering reads, and so demanded the balancer's
  storage-group lookups (a key built from an enum's `toString`, item 30)
  (`gc/compose/Independence`, `ContainerSmtCodec#fieldOperands`).

Offline over r8 (`tools/regress/offline-ab.sh --round r8`, `/bigtemp/vnr3ne/ab/agent-a0f-gate8-r8`)
HEAD claims `SAT_CANDIDATE` `CLOCK_SKEW`, `polarityDecides`, on 17 paths (main: 6), moving the
NameNode's four key-expiry clocks (`REGION.08ab84c9`) and the DataNode's (`REGION.ba3902cd`) off
their readings, with no BLOCKING gap from COMPOSE or the last EXPLORE wave (main: 17 and 18); only
the recording's own three shared addresses remain. Over r3's corpus (`agent-a0f-gate7`) it admits
47 paths (main: 2) and claims the same, and valuation 0 needed `ClaimPolicy#byDisjunct` (whole,
undecided after 30 minutes; each path alone, about a second); over r4 (`agent-a0f-gate7-r4`) it
claims the same on 41 paths, and hdfs-17899-bug2 claims `MARKER_FLIPPED` in 486 s. `cone.py` puts the DataNode clock and the first
NameNode clock (`in.d977bf12`) in the witness path's cone, so a NameNode clock now reaches the
DataNode check; the other three NameNode clocks move only because `clock_order` keeps that node's
readings ordered, which the cone does not follow, so the cone gate would still fail on them.
That claim rested on free constants: the balancer's block-key expiry (`HOFF.9a4963b5`,
`HOFF.3220fe99`), joined in a move task's arm closure, was bound by no family. HEAD binds it
(`ComposedFamilies#handedOn`), and over r8 (`/bigtemp/vnr3ne/ab/r11741-exp-r8r7`) all 17 paths are
then unsatisfiable with every root free (`PATH_SELF_CONTRADICTORY`, `NO_SUPPORTED_WITNESS`): the
NameNode arms deliver that expiry as constants. The workload's `pinBlockKeys` rotated the keys before
`startRecording`, so the key the Balancer fetched and cached had an expiry no recorded clock wrote, a
different constant in every replay. The HDFS tree (`gc/hdfs-11741` `5cff0e12b1f`) now rotates once
inside the window before the Balancer's fetch; no round has run on it yet.
hdfs-17960, hdfs-17897, hdfs-17899-bug1 and hdfs-17967-pathB keep their claims (r3, r7).

Round `rb1` (this branch before the merge of main `69edf0c06`, fresh seeds) failed hdfs-17967-pathB
and pathC: their witness moved `HDFS.BLOCK_KEY.SERIAL_NO`, not a door. Main's `7e0d8b14e` moves a
flip query's non-control handoffs with their own run's arms, so a wave-0 flip at
`retrieveDataEncryptionKey#u8` moved the target DataNode's block keys with the serial, while the
worker DataNode's SASL key id stayed: main's weave exports it as a constant (R1-ROOTS' `ra1` states
it as the worker's heartbeat handoff). The replay was answered with key id 119532 where its producer
sent 119533, and COMPOSE pinned the answer as a literal. HEAD binds an answered handoff by its family
(R2). Offline over `rb1` (`/bigtemp/vnr3ne/ab/r11741-2-rb1`), both claim `MARKER_FLIPPED` on an IPC
request door (`REGION.763d087e`), with no unbound boundary variable (`cone.py`); pathC's witness
needs a CONFIRM replay. Over r8/r7 (`r11741-1-r8r7`, `r11741-1b-r8r7`) the other eight HDFS claims
are main's, and hdfs-11741's and hdfs-17967-pathA's composition is the branch's before the change
(`r11741-3-branch-vs-fix`).

The ad-hoc checks have found no new bug; the only confirmed ad-hoc witnesses ever were two
CLOCK_SKEWs on token-expiry checks, judged to be HDFS's clock-sync assumption.

## R1. Symbols come automatically from the fatal slice

| capability | status | where | missing |
| --- | --- | --- | --- |
| Backward data slice from the declared throw across methods (arguments, returns, callers, CHA dispatch) and field writers | done | `gc/causynth/SeedBackwardStaticAnalyzer` | Application classes only. The field jump is instance-insensitive. |
| Control dependence inside a method | done | `gc/causynth/SiteControlDependence` | The CFG is a `BriefUnitGraph`, so exception edges are ignored and a catch handler a fault leads to has no guard. The slice uses may-reach; the scope map's guards use post-dominance: two relations. |
| Control dependence across methods, threads and the wire | partial | `SeedBackwardStaticAnalyzer` (callers of field writers, constant stores up to 3 calls up) | Nothing across a thread start, an executor submit or a message. |
| Library-typed state (the receiver of a non-application call) | not done | `SeedBackwardStaticAnalyzer#localValueUses`, `#isValueLikeLibraryInvoke` | `x = lib.m(k)` depends on `k` only, except modeled containers, String/StringBuilder, unboxing and structural accessors. State behind a `ConcurrentMap`, `NavigableMap`, `AtomicBoolean` or cache never enters the slice. |
| CLOCK roots by category | done | `gc/causynth/RootCatalog#clockTicks`, `#wrapsAClock` | Only the JVM clocks and zero-argument int/long wrappers under constant arithmetic, found on `call_return` edges. Not `java.time`, a clock read through a field, or a delegate outside the scope. |
| A node's clock: planted, composed and claimed as one | done | one clock = one node, one JVM clock, one tick (`gc/contract/Clock#same`; the source read off the wrapper's body by `gc/causynth/RootCatalog#clocks` and carried by the scope map, the plan action and the mint row); a replay's plant is a jump its node's clock runs on from, in the recording's order (`gc/runtime/NodeClocks`, `RootMint#materializePrimitiveValue`), and a clock's mint row states the instant the run used and its `clockSkew` (`RootMintRow#hostReading`); COMPOSE orders each clock's cells by the recording's seq, places a cell the seed never read by its session's elapsed time, and relaxes a link the recording read the other way round (`gc/compose/Composer#clocks`); the claim names only the jumps, pinned back in seq order (`ClaimPolicy#leastClocks`, `#runsOn`, `#jump`, `#withMargin`); CONFIRM plants the model's clock world, its jumps alone on every cell the composition anchors, each off the composition's reading, and a session realizes a claim only if its clocks are those (`gc/explore/ConfirmMain.Moved`) | Only declared CLOCK sites move; an undeclared read of the host clock stays at the host. A flip query's cells are unordered, so an obligation may plant a later cell behind an earlier one (a jump back). A reading the replay runs before the jump that precedes it in the recording's order was planted reads the host (or an earlier jump). A row recorded before the `clockSource` contract (every round up to `r9`) states no source, so COMPOSE orders none of its cells. |
| FAULT roots at transport doors | done, declared per system | `gc/causynth/DoorWeave#apply` (runs before analysis); `gc/plan/StaticScopeMap#declaredFault` | Doors come from `DOOR` rows. A marker counts as declared only if its transport has a row. Only the first call of the named callee is woven. |
| READ placeholder roots | partial | `StaticScopeMap#markReads` | Only an accessor with an unwoven (JDK) body, a primitive return, and a location another region stores: in practice `AtomicInteger`/`AtomicLong.get`. |
| Configuration roots | not done | `gc/causynth/StaticSymbolicSourceDiscovery`; `gc/runtime/RootMint#configuredSource` | Only a hand-written tree hook `CausynthSymbolicSource.symbolize` mints one, and only on a primitive instance field. There are six such hooks in every block-key tree and one in 17960. |
| Randomness | deterministic, not symbolic | `gc/causynth/CausynthPipeline#replaceRandom`; `gc/runtime/Randoms` | `ThreadLocalRandom` and `SecureRandom` are not replaced. |
| Method-return symbols | partial | VM `Integer.parseInt`/`Long.parseLong` and other unmodeled primitive returns; `gc/compose/SmtLowering#methodReturn` lowers the call the node states (VM f14 `call`), and `#methodTerm` a `MethodExpression`'s, by `#knownCall`: `parseInt`/`parseLong` of a String and `valueOf`/`toString` of an integral as relations, a parse of a lone decimal rendering as the value rendered (`gc/compose/StringIdentities#parsedOperand`), another callee pinned to its stated value by a named assertion (gap `MethodReturnPinned:<symbol>`, DIAGNOSTIC) only when nothing its arguments rest on moves | Other library returns are not symbols. A node stating no call (a VM before f14) is refused (`MethodReturnCallUnstated`), so a path through one drops. A non-ASCII digit is outside the parse relation. |
| Scope growth to a fixpoint | partial | `gc/plan/ScopeFrontier`, `gc/plan/ScopeGrowth`; `run_engine.sh` `campaign_analyze_grown_scope` | The default budget is 24 classes, and the audited sweeps hit it. Growth is switched off (`causynth_scope_growth_budget=0`) for every named case. CHA spends the budget on every implementation. Protobuf classes are never grown into. |
| Root admission | over-admits | `gc/causynth/RuntimeSelectedRegionFinalizer#readsARoot` | Every occurrence that reads any clock or marker is admitted, whether or not the slice needs it. |
| Loop-body roots (a service-loop iteration is the activation) | done | `gc/causynth/StaticProgram`; `CausynthPipeline#loopBodyEntry` | An unsupported loop shape throws `LOOP_BODY_ROOT_ENTRY_UNAVAILABLE` at INSTRUMENT and ends the campaign. |
| Demand a root when the anchor's predicate is concrete | not done | `gc/explore/ClosurePlanner` demands only symbolic operands of the target guard and predicate | When the predicate is concrete, the closure is the anchor alone, the wave has zero obligations, and COMPOSE refuses every path as "decided concretely on its healthy arm". This is 195 of 260 finished sweep verdicts. |
| Restart and delivery-delay roots | not done | — | — |

## R2. Values keep their expression across processes

| capability | status | where | missing |
| --- | --- | --- | --- |
| Causal context across Hadoop IPC and SASL | done (tree adapter) | the Hadoop shim `src/shim/java/org/apache/hadoop/ipc/CausynthMessagePropagation`; `gc/runtime/MessageDoors#outbound`, `#inbound` | Carried in new `.proto` header fields and in hand-edited `Client`, `Server` and SASL classes in every tree. |
| Causal context across HTTP and ZooKeeper (Solr) | done (tree adapter) | `MessageDoors` store doors `#stored`, `#fetched`, `#notified`, `#consumed`; Solr tree `CausynthHttp`, `SolrZkClient` | A read of a stored version outside a watcher callback gets nothing. The Overseer queue and polling reads carry no anchor. |
| Anchor lookup | same JVM only | `gc/runtime/RuntimeTraceContext`; `gc/runtime/Interactions` | The header carries no producer endpoint. The anchor is looked up by correlation in a JVM-global table capped at 8192 entries; a receipt it no longer answers files `LINEAGE_LOST` with the eviction count. |
| Declared ports (`WIRE_FLOW` rows) | done, hand-written | `gc/causynth/WireFlowCatalog` | Written per case: block-key-id, block-key-expiry-date, namenode-data-encryption-key-id, data-encryption-key-id (HDFS); two routing-rule rows (SOLR-18413). |
| Ports derived by rule | partial (protobuf scalars of RPC messages) | `SeedBackwardStaticAnalyzer#deriveWirePort`, `#rpcMessages` | Only a primitive or String getter of a protobuf message that a protobuf service method's request or response holds, whose `Builder.setF` call is in scope. No repeated, enum, bytes or nested fields. No frame. A declared row wins over the derived port. By type, so a message an RPC carries and a stream also writes (`ExtendedBlockProto` in a DataTransfer op) exports at setter calls that reach no door. No run shows a derived port carrying a value end to end. |
| String-carried values (the SASL user name, JSON in ZooKeeper) | not done | — | They need hand rows plus tree rewrites (`Integer.toString` in `SaslDataTransferClient`; SOLR-18413's `SliceMutator`). |
| Codec holes (WIRE-CODEC) | partial (contract, lowering, COMPOSE/EXPLORE/CONFIRM; no producer of hole rows) | `gc/contract/Hole`, the hole fields of `ExportRow`/`AttachRow` (`codec`, `keyPath`, `hole`, `messageKey`), `pairedBy ENVELOPE` and `RowInvariants` invariants 2 and 5; `GapKind.CODEC_MISMATCH`; `gc/contract/WireDeclarations` (CODEC, CODEC_VIEW, KEY, TRANSPORT, EXCHANGE rows); `gc/plan/CommunicationCatalogContract#codecPortId` and the `CODEC_PORT` row's fields; the §6.2 lowering identities (`gc/compose/StringIdentities`: `valueOf`/`concat` operands as `toString`, parse of a decimal rendering, a boolean rendering against a literal, split of a template, piece-wise `equals` of two templates) and the §6.1 literal of each sort (`gc/compose/VmTermLowering#smtLiteral`, COMPOSE's callers and a flip query's through `gc/explore/SmtText#literal`); the §6.1/§6.3 hole arm (`gc/compose/VmTermLowering#holeArm`: decoded sort, Java widening, a rendering read back, nullness; `gc/smt/Arms#sameMessage` pairs a hole with its own message's export; relays as nested families, `gc/compose/ComposedFamilies#hole`), a String hole's answer as its JSON string literal (`gc/explore/ObligationFactory#answer`), and CONFIRM's hole edge (`holeTexts` in the claim, `gc/compose/ComposedFamilies#holeTexts`; `messageKey`/`value` on the WIRE edge, `gc/explore/ConfirmMain`, compared by `gc/runtime/Confirmation#attached`) | Nothing writes a hole, a `CODEC_PORT` row or a `wire.jsonl`, and nothing reads the declarations: no port rule, codec hooks, walker or VM leaf natives, and no library catalog. The catalog still stamps schema 5. The identities never look through a read, so on HEAD they fire only where a rendering meets its parse, split or comparison without a heap location between them (the SASL key id is split into an array and read back). Only synthetic hole rows exercise the hole arms, answers and edges; no runtime calls `Confirmation#attached` with a hole's message key and text yet. A hole's value is held in CONFIRM only where it rests on no clock (a replay reads its clocks afresh), and a message key only for a store's version (an exchange's correlation id is its own run's). The VM still wraps every read in a `ConsumerBoundaryExpression`, so `SmtLowering#lowered` keeps seeing through it. |
| Receiver-side symbol `v_H` | primitive leaves only | `gc/runtime/HandoffMint#addPrimitiveLeaves`; `gc/runtime/WireExport` | String and boxed leaves are substituted with the producer's expression, with no family. A VM export or attach refusal is a gap naming the occurrence, port and status (`WireExport#refused`): an attach outside every admitted activation a DIAGNOSTIC `ADMISSION_GAP` beside that activation, stated unselected; one inside an admitted activation DIAGNOSTIC `UNSTATED_VALUE`, which refuses at COMPOSE only the paths and arms whose closure reaches that occurrence (`Composer#frameRefusals`). The closure does not yet read the `ADMISSION_GAP`. |
| Outbound staging | per thread | `gc/runtime/SymbolicMessageEnvelope` | Staged values ride the thread's next outbound message, so a message built without passing a door can lend its leaves to the wrong message. Capped at 64 entries. |
| Composer merges both sides (MESSAGE families) | done | `gc/compose/ComposedFamilies`; `gc/smt/Arms` | Only arms of the same interaction slot, from sessions of compatible worlds. An unpaired attach refuses its path, answered or not: an obligation's answer is bound by the family like an arrival, never pinned as a literal (`Composer#handoffRead`), and a handoff variable the path's session minted no attach for refuses it (`#reachedHandoffs`). An arm binds every handoff its conjunction names by nested families, those its closure reads included (`ComposedFamilies#handedOn`). |
| DataTransfer ops, HDFS HTTP, `Http2SolrClient` forwarding, javabin/JSON bodies | not done | — | No anchor and no values. DataTransfer ops are daemon-tick roots. |

## R3. Shared state in one JVM is tracked and re-pairable

| family | status | where | missing |
| --- | --- | --- | --- |
| Integral instance fields (boolean…long) | done | `gc/causynth/CausynthStaticFacts#trackedKind` (`VALUE`); `StaticScopeMap#decidingCells`; VM `observeField`, `sharedFieldVersions` | Tracked only when the read reaches a branch within 8 flows and the slice stores the field. |
| Unobserved writes | done | VM `sharedFieldVersions`: a tracked access and its log entry are one critical section, so a loaded word no version stored is a writer no hook saw; the read names a retained version that stored it (not exact: a newer version overwrote it), else publishes an UNOBSERVED version, and the location is marked incomplete by name (`incompleteReasons`, `unnamedWriter`). Every read states `observedExact` (a reference's word is its referent's id); `gc/smt/VmRows#joinable` joins an exact read at an incomplete location | A container read states no word, so an unhooked container mutation is not detected. |
| Wrapper-typed fields (`Boolean`, `Byte`, `Character`, `Short`, `Integer`, `Long`) | done | `CausynthStaticFacts#versionableField` admits an integral wrapper as a value cell (a `READ_SITE`); `StaticScopeMap#sameType` joins its write rows by the value's type (`JavaPrimitiveBoxing#valueDescriptor`); VM `observeField` observes it, and its stores and reads state the box's primitive word or the null word (`SharedFieldVersions::boxed_word`); a read is the value's sort | A `Float` or `Double` field. |
| Reference fields; a container behind a replaced reference | partial (PLAN, VM, rows, EXPLORE, COMPOSE, CONFIRM) | `CausynthStaticFacts#trackedKind` (`REFERENCE`: a reference field a store re-points); `StaticScopeMap` READ_SITE `trackedKind`, `publishedFrom` write sites, `#constructionGuards`, `#carriersAt` (a write joins a carrier whose site stores its location's kind, `#stores`, and whose declared type may hold the row's class, `#mayHold`: a `Map` field holding a `ConcurrentHashMap`; an array element joins none; EXPLORE and COMPOSE alike); `SeedBackwardStaticAnalyzer#publishMutation`; VM `observeField` (a reference cell, instance or static; bound by `runtime/ConcolicVmBroker#observeField`), a reference store's `referentState` (`SharedFieldVersions::prepare_referent`, `ContainerSupport::referent_state`), a reference read's identity `concreteValue`; rows: `contract/WriteRow#referentState` (or `#referentStateRefused`, `RowInvariants` invariant 12), admitted by `runtime/SharedStateCapture#referentFault`, refused by name when the container's log or version is no row (`RowPublication#unrowedReferent`; at IMPORT DIAGNOSTIC); `ReadRow#returned` spells an identity, which `Composer#pin` binds; EXPLORE: `explore/Corpus#referentStates` (a demanded reference read demands the writers of each state its eligible stores delivered, `SmtLowering#statesOf`); COMPOSE: `gc/compose/SmtLowering#query` (a query through a movable `owner` answered per candidate identity from the states the reader could have seen through each store of it, floored at that store's referent, each chosen by a `nest__` selector bound to the arms delivering its store, a read movable only in its own path, `#path`; the run's own map answers as the run saw it through the store the read observed; a later state rests on its writer's decisions, `ComposedFamilies#stateClosure`; `#statesOf`, `#storeChoice`, `nest_family__`), `Composer#constructionGuards` (from `--static-scope-map`), `Composer#pinnedOwners` (a mutation through the reference, or a store of a wrapper or view over the map, keeps the run's pairing); the claim: a selected state arm's `referentStates` (`SmtLowering#stateChoices`, `ClaimPolicy`, `ComposeMain#referentStates`); CONFIRM: `explore/ConfirmMain` holds the reference read to the chosen store and the query's read to the chosen state's write, each with its ORDER rows, and a session is its own confirmation only where its reads saw every write the model chose; synthetic SOLR-18406 in `ComposerTest#aQueryThroughAReplacedReferenceIsAskedOfTheMapItHolds` claims CLOCK_SKEW, and `#aReplacedReferencesOtherMapIsEachStateTheReaderCouldSee` a STATE_PAIRING_FLIPPED naming the mutated map's state | Only round r4 has recorded it, on `vm-r3`, whose read-out emptied every version envelope past 32 MB of a page (947 location logs of SOLR-18406; fixed in `SFV#write_versions_envelope`, image `vm-r3b`); a VM image before R3-REFCONT WP2 lacks `observeField`, and a replay on it is refused before its workload (`ConcolicVmBroker#requireCurrentCapabilities`). `cone.py` follows no writer family (WP7). Carrier matching has no class hierarchy, so a field of an application class or interface agrees with any reference. A chosen state whose query no container read answered (a `referentStates` row with no reader) refuses the confirmation by name. STATE arms from other sessions (D3) are not built. |
| Containers | partial | VM models maps by the Map contract over `HashMap`, `LinkedHashMap`, `ConcurrentHashMap` and `Hashtable` (by the receiver's class, `ContainerSupport::capability`; views and `Collections` wrappers are their backing map, `ContainerSupport::backing_container`), with `getOrDefault`, `putAll`, `putIfAbsent`, `replace`, `compute*`, `merge`, `replaceAll`, `forEach` and a view's `removeIf` (a callback runs with propagation, `MethodSymbolizer::enter_callback`), plus `HashSet`, `LinkedHashSet`, a `KeySetView`, `ArrayList`, `ArrayDeque` (`symbolicMap`, `symbolicSet`, `symbolicList`); a relation through a guarded reference read states it as `owner`; the slice and COMPOSE's sorts classify by interface (`gc/smt/JavaContainerTypes`) | The VM does not model `TreeMap`, `TreeSet`, `ConcurrentSkipList*`, `LinkedList`, `CopyOnWrite*`, `PriorityQueue` or blocking queues (R3-REFCONT WP3b/c). COMPOSE lowers `owner`, `READ_OR_DEFAULT` and `PUT_ALL` (a source whose chain bounds its keys) and refuses an `ENTRY` value by name; a `READ` whose value states no class compared with a scalar (`remove(k, v)` over boxed values) is a sort conflict, refused. A container query's read states no answer (VM `ContainerSupport::query_state`), so such a read is pinned only through a join; COMPOSE holds a re-paired container whose query read something is asked through to the run's pairing (`OWNER_PINNED_BY_CONTAINER_READ`). A query through a `Collections` wrapper held in a reference cell carries no `owner`, so COMPOSE keeps that cell's family to the run's pairing (`OWNER_PINNED_BY_WRAPPER`). `values().removeIf`, a HashMap `replace(k, v)` that answered null, a visiting callback call past 64 elements, a fifth nested callback, a `removeIf`/`replaceAll` unwound by an exception, and a list's `removeIf` abandon the state. |
| Atomics | partial | PLAN: `gc/plan/SharedFieldFlow` (one table: `get()` reads, every write of the four atomics writes `value`); VM `symbolicAtomic` (`AtomicInteger`/`AtomicLong` read-modify-write, linearized at the compare-and-swap that versions it), `unsafeAccess` (`lazySet`, `getAndSet`, a CAS, field updaters: Unsafe writes versioned with their captured operands) | Only the two atomics' arithmetic is a symbolic relation; an `AtomicBoolean`/`AtomicReference` compare-and-set records its decision over the value it compared. `AtomicReference.value` is a `REFERENCE` cell the VM observes. |
| Arrays | partial | VM array stores (the first symbolic store into an array starts its element's log); a load at a concrete position resolves through the recorded writes, each stating the word it left (`ContainerSupport::recorded_element`); `System.arraycopy`/`Arrays.copyOf` and `clone` carry element values and versions (`heapCopy`) | A copy past 16384 elements drops a shadowed destination's state (named). An object copy that checks each element's store versions no tracked destination element (named `ARRAYCOPY_STORE_CHECK`). |
| Static, float and double fields | partial (VM) | `CausynthStaticFacts#trackedKind`: a static reference is a `REFERENCE` cell (`static: true`); VM `observeField` keys a static field by its class mirror | PLAN observes none of a static's accesses; static values, `float` and `double` are not tracked. |
| Guarded concrete stores | done | `gc/runtime/GuardedStoreSites#of` (one row per scope-map store site: method, `FIELD a/b/C.f` or `CALL <name>`, guards); VM `SharedFieldVersions#guarded_field_store_admitted` (putfield/putstatic: an INITIAL of the replaced word, then the WRITE, no path guard), `ContainerSupport#guarded_mutation` (containers) | A store site is told apart by what it stores, so two calls of one name (or two stores of one field) in one method share a row. Array-element stores are never admitted (the scope map lists none). |
| STATE families at COMPOSE | partial | `gc/compose/Composer`, `ComposedFamilies#stateFamilies`, `Arms#stateArms` (the observed writer's arm is the write its reads saw; a location whose reads no one arm states is a BLOCKING `UNSTATED_VALUE`; alternatives unless a read met a writer the VM's log never named, `ReadRow#unnamedWriter`; the version bound alone keeps them); a location a reader mutated a container through, or one holding a wrapper or view of a map, keeps the run's pairing (`Composer#pinnedOwners`) | Only for reads at the anchor occurrence, only from writers in the same session, and never for a class-owned location. Location owners are per-run VM ids (`gc/contract/LocationId`), so no state joins across sessions. `cone.py` does not follow writer families. No run has produced a STATE_PAIRING witness. |
| A field read through a reference a STATE family re-points | partial | `gc/compose/SmtLowering#projection`, `#perCandidate`, `#candidates`, `#fieldOf` | Only when the owner is the anchor read itself; an owner reached through an inlined chain (a symbolic list index) keeps the run's cell. A candidate's field is answered only by one write before the object was stored or, never written, by reads stating one value; a field mutated after publication (R3-REFCONT §1.4) refuses its arms (`CANDIDATE_UNANSWERED`). Only objects of exactly the run object's class. Offline evidence (`/bigtemp/vnr3ne/analysis/proj/v2/index.txt`): with the s46 witness's `M_J_return28` stated (validation only, so its path composes), latestCommit's four arms read generations 1, 1, 2 and 3 of four distinct commits, and the fatal holds under the observed arm only; before, all four read commit 1182's 3 and all four were fatal. |

## R4. Large-scale ad-hoc checks on HDFS and Solr

| capability | status | where | missing |
| --- | --- | --- | --- |
| Find guarded throws; find the checks a test reaches | done | `tools/adhoc/sites.py`, `coverage.sh` (exits with the test's own status), `reach.py` | A text scan. JaCoCo counts the whole JVM, not the recording window. |
| List a system's cluster tests | done | `tools/adhoc/workloads.py` (a class-file reader: every JUnit 4 or Jupiter `@Test` method, declared or inherited, that `runtime.JUnitLifecycle` can call, of a test class that, itself or a superclass, names `system.sh`'s `system_cluster_class`; `@Ignore`/`@Disabled` left out) | A test that needs a JUnit rule or runner the lifecycle does not honour is listed and fails at coverage. |
| Select checks by the engine's own static slice; declare their targets | done | `run_engine.sh` `slice` (SEED's static half, scope grown, no workload); `tools/adhoc/select.py declare` (every reached check a sweep can run, skipping, and naming on stderr, a timeout's check, a workload whose test failed under coverage or starts no node, a moved line), `slice.sh` (one slice per check on the lifts, `$GC_OUT/static/<key>/<check>/`, kept per build key), `score.py` (the roots the slice reaches back from the throw's branches: clock, fault, `READ`, cross-region store, wire crossing; keep = a root within 4 edges, calibrated on 260 h4/q* verdicts), `select.py rank` (`selected.jsonl`, three per class, a 5% calibration tail of dropped checks), `targets.py`; `gc/causynth/ExceptionTargetLineResolver` | The ~2000 reached checks are not yet all sliced under the current build key (70-100 s and 3.2 GB RSS each; the first nightly does it). keep is a weak filter: of the checks it keeps, 66% still had their anchor decided concretely (88% of those it drops). The score saturates beyond keep. A door counts only when a store's method calls it within three calls of the slice: the IPC doors the block-key witnesses flip show only as a wire crossing. A declared config root (hdfs-17960) is no root kind the score names. A throw in a lambda body or an anonymous class resolves, but a slice that starts in a `lambda$…` body stops at its captured arguments (no `invokedynamic` call edge). |
| Fan out over ten lifts under a memory gate | done | `tools/adhoc/sweep.sh`, `fanout.sh` (a job's `NEED_MB`, resume over `<n>.exit`); `tools/lib/gc-env.sh` (`GC_OUT`, `CAUSYNTH_HOST_LEDGER`, `LIFTS`); `run_engine.sh` `campaign_host_try_start` (need and ramp per row), `campaign_head_charged` (a head's engine JVMs and replays), `campaign_worker_slot_hosts` (rotated per wave); no start leaves a host more than `CAUSYNTH_HOST_MAX_USED_PCT` (70) percent full (the reserve is 30 % of its `MemTotal`), and `/bigtemp/vnr3ne/bin/pick-lift.sh` (`onlift.sh`, `offline-ab.sh`) places by the same ceiling | A charge is the stated heap, not the measured RSS, and it lapses after the ramp: a JVM that grows past it later is seen only in `MemAvailable`. `offline-ab.sh` places through `pick-lift.sh`, not the ledger, so a gate's case and a campaign's starts do not see each other's ramps. Every obligation solver loads the whole corpus (5-7 GB RSS; defect 11). |
| Build key and nightly sweep | partial | `tools/adhoc/buildkey.sh` (`<experiment>-<12 hex>`: the jar's entries, the tree's commit, the scope declarations; names `$GC_OUT/static/<key>/` and `$GC_OUT/prescreen/<key>/`, computed by `slice.sh` and `prescreen.sh`); `tools/adhoc/nightly.sh` (freeze the newest `regress-pass-*` commit as `~/gc-run/n<date>-<experiment>` with its tag's VM, lock it in `$GC_OUT/snapshots-in-use/`, `manifest.json`; coverage per tree commit; declare, slice, rank with the 5% calibration tail, pre-screen per build key; `sweep.sh`, one re-run of the cases lost to the infrastructure; `triage.tsv`, `findings.tsv`, `report.md` by `funnel.py`); `tools/rounds/snapshot-gc.sh` (removes a snapshot no lock and no process names, `tools/lib/alive.sh`) | No `regress.sh`: the `regress-pass-*` tag is placed by hand. No nightly has run. |
| Disk and quota gate | done | `experiments/accept/accept.sh` `acc_free_gb`: `MIN_FREE_GB` free on the filesystem `OUT` is written to, and a refused 1 MB write there reads as 0 | — |
| Time bounds | partial | case budget 5400 s (`sweep.sh`); obligation replay 2400 s (`replay_timeout_s`); seed replay `seed_replay_time_factor` (40) × the recorded workload's time, at least `replay_timeout_s` (`run_engine.sh` `campaign_session_replay`); a bounded run's process group is gone before its caller reads what it wrote (`run_under_wall_clock_bound`), and an obligation that times out or whose worker does not finish is its own `NOT_ADMITTED` answer (`campaign_obligation_replay`, `campaign_obligation_unfinished`) | The seed recording has no wall-clock bound of its own; only the case budget ends it. |
| Replay schedule stalls | done | `gc/runtime/ScheduleLog#watchdogLocked`, `#computingLocked` | The engine's own threads (`causynth-*`) never defer a give-up, and a let-go no longer restarts the stall's clock: a never-coming event costs a timeout plus a 2 s grace when no workload thread computes, and at most eight timeouts plus the grace when one does (s49: 17 stalls of 120 s, two per episode). Every workload thread's CPU counts, because which thread owes a slot cannot be seen between its events. |
| Replay polling past the recording | done | `ScheduleLog#waitsAtLocked`, `gc/runtime/ClockLoops` | While the prefix stands, a loop past its recorded count polls once per move of the order (s49: 6862 such WAKEs spun free on the wall clock). A loop that reads a CLOCK root stays free; the check is by method on the waiting stack, so a clock read in a callee that returned before the wait is missed. Past the cut such polls still run free. |
| Stop at a first fatal | partial | `region_path_stop_at_fatal` (`gc/explore/ExploreMain`) | Only `solr-adhoc` sets it. |
| End a focused replay once its question is answered | partial | at its witness (`AT_WITNESS`) or at the refusal that decides every obligation it carries (`AT_REFUSAL`): `gc/runtime/ConcolicResultPublisher#conclude`, `FocusedReplay#refusedAt`; a decided replay publishes no session (`RowRuntime#closeSession` withdraws it to `<worker>/refused-sessions/`; `run_engine.sh` `campaign_obligation_replay` withdraws one a failed move left listed, `campaign_await_remote_result` waits until the head's listing drops it); the settle of every end is bounded by progress (`ConcolicResultPublisher#awaitSelectedResultPublications`: 30 s with no loop body, no settled activation or publication and no CPU on the publication thread), and a stranded activation's own terminal closes its VM region (`ConcolicRegionRuntime#closeStranded`) | A flipped obligation's replay runs to the workload's end unless its witness ends it. Only refusals filed during the run decide; an inherited flip never reached or a missing mint row is still found at the end. |
| Where a campaign's wall time went | done | `tools/analysis/timeline.py` (stage metrics, file mtimes, the log) | A head's wait for memory is inside the stage or gate that started the JVM; the log counts the waits, not their time. |
| One recording per workload for several checks | partial (shared SEED and seed replay) | `run_engine.sh` `campaign_record_batch` (each target's slice from `causynth_static_root` frozen into `targets/<name>/`; one recording woven with every target's skeletons merged by root and every target's grown scope, `campaign_union_static`; `runtime/record-summary.json`), used by `record` (the pre-screen, bounded by `record_timeout_s`) and by a batch campaign (`campaign_batch`: a campaign given `causynth_static_root` runs no static pass, records once, plans each activated target on its own slice, groups the plans so that each group's union is one plan, `plan.PlanUnion` (a target joins the first group where every occurrence both plan is the same task and every site both observe the same observation), weaves, seed-replays and imports each group once, `campaign_batch_group`, then runs every target its group's seed reached from EXPLORE on, all at once, `campaign_batch_target`, each in `targets/<name>/` with its own campaign root, log and result; PIPELINE §2b); `runtime.CausynthTraceRecorder` (the trace read once, each `--target` aggregated on its own slice over its view of the skeletons merged by root, `campaign_region_view`: every region the recording opened, its own selection at the roots it plans -- a target folded into another's region is found there, where its own skeletons alone lost it as `NOT_IN_WINDOW` --, a refusal its own `NOT_IN_WINDOW`, `TARGET_BRANCH_NOT_OBSERVED`, `POLICY_ABSENT`, `NO_REGION` or `ERROR`, with the target occurrences and those that took the fatal arm, `fatalOccurrences`); batch cases `B<n>` (`batches.tsv`, `targets/B<n>.yaml`, `tools/adhoc/batch.sh`); `tools/adhoc/cover.py` (a greedy cover of the selected checks by their tests, at most 16 per recording, two tests per check; then one batch case per workload of the activated pairs, at most four checks), `prescreen.sh` (a recording kept per build key, named by its workload and a digest of its checks), `sweep.sh` (`STATIC_ROOT`), `triage.py` (a row per check of a batch) | Two targets whose plans hold different tasks at one occurrence replay apart: both reaching their own target there (one task carrying several target branches is not in the runtime, M1/M2), or their slices weaving one region's branches in different methods (`branchMethods`; each target's slice is still its own Soot pass, WP3.1, one scene, not done). The three token checks of `mirror` (wp3-5) share 72-82 of 85 occurrences pairwise and still replay as three groups, for both reasons. The occurrence addresses carry the other targets' root frames, so they are not a solo campaign's (`occurrences.tsv` pins do not carry over; batches use `first`). |
| Triage | partial | `tools/adhoc/triage.py`: CONFIRMED, REFUTED (`SAT_UNCONFIRMED`, with the confirmation's reason), NO_WITNESS, STOPPED (with the reason its logs state), DEAD (no lift runs it any more, `tools/lib/alive.sh`), RUNNING, PENDING | `UNSAT_CLOSED` is folded into NO_WITNESS. |
| Native reproduction of a confirmed witness | partial (fault markers) | `run_engine.sh` `campaign_reproduce` (REPRODUCE, after CONFIRM: `reproduce_runs` runs of the recording weave on the stock JDK, each aggregated for the target; `final/reproduce.json`, copied into `result.json` as `reproduction`); `gc/explore/ConfirmMain --plant` (CONFIRM's world, `#world`, as marker rows keyed by call site and mint occurrence id); `gc/runtime/RecordingPlant` (`Debug.makeSymbolicBoolean` answers a row at an enclosing occurrence of its id, a `PLANT_APPLIED` trace row); `CausynthTraceRecorder` (`plantsApplied`, `fatalOccurrences`) | A world that skews a clock, answers an attach or assigns a config or integral root is not planted (phase 2: the clock and config reads of the recording weave). The runs hold no schedule, so a rate below one ranks a finding and never refutes it. |
| Dedupe and rank findings by mechanism | done | `tools/adhoc/findings.py` (signature: the check's TARGET_SITE, the finding kind, and per moved root its kind -- a fault door's marker is FAULT --, site method, callee, node role, causal context and a clock's skew bucket (the model's instant off the reading the composition anchored the cell to, the manifest's `roots`); read from `result.json`, the plan's input action and the selected session's `roots.jsonl`, all kept by PRUNE); `$GC_OUT/findings/ledger.jsonl` (new, known, dismissed by `dismissed.tsv`); `--annotated <system dir> <tree>` (`nightly.sh` passes the sweep's tree): a finding whose declared target is a known bug's marked throw (`tools/lib/annotated.py`) is known, its `known bug` column names the cases, and `funnel.py` lists the known bugs a sweep found again; the weight multiplied by 1 + the native reproduction rate (`result.json` `reproduction`) | The mediated bonus reads `score.json` by TARGET_SITE, so the static root must be the sweep's own build; the IPC door roots of the block-key witnesses are not in their slices (only as a wire crossing), so they get no bonus. A CLOCK root row from before the `clockNanos` contract is refused by name. |
| Automatic cluster as a workload | partial (tree patches) | HDFS `CausynthCluster` automatic mode (`hadoop-hdfs-unified`, the one HDFS tree of the named cases and the sweep); Solr `CausynthSolrCluster` | Real-time bounds are patched per system; upstream HDFS workloads are limited to one DataNode (`ThreadLocalRandom`). |

## R5. Correct .smt for the Solr cases; the nine HDFS cases keep passing

See Acceptance above. What remains (the branches are in README §0.3):

- hdfs-11741: the 22 blockers are fixed off main. A claim names only a clock's jumps (a cell that
  runs on from the cell before it is no move), so the three NameNode clocks that moved only through
  the `clock_order` constraint are no longer named; no round has checked the cone on HEAD.
- SOLR-18406: passes on this code (`a37f4`); no round on HEAD.
- SOLR-18413: the `isExpired` flip is SAT with MigrateCmd's clock skewed forward, and its replay
  reproduces the fatal; a fatal condition that is concrete in a replay must state its phi (IMPORT
  invariant 9). The store door files what a write carried after the schedule's SEND lets the queue's
  consumer run (`gc/runtime/MessageDoors#stored`, open defect 28), which can leave the Overseer
  queue's attach unpaired.

The offline regression gate `tools/regress/offline-ab.sh` (with `ab_compare.py`) compares a
candidate jar against a baseline on a recorded round, stage by stage, with no replay. It reads a
round as HEAD reads it, so it needs a round recorded by a build whose rows HEAD still reads (r7 and later). `AB_BASELINE_REPO` runs the baseline under its own checkout's case
declarations, for a change whose declarations move with the jar. Every stage gates on bytes: SEED (with its woven classes) and PLAN
are byte-identical across lifts and runs (`/bigtemp/vnr3ne/analysis/det2/s6/`: hdfs-17897,
11741, 17899-bug1, 17960 and solr-18413 on five lifts, two with the scope copied in opposite
orders, three under other JVM identity-hash generators).

## R6. No per-case code, no dead code, no fallbacks

| item | status | where |
| --- | --- | --- |
| Engine code naming a system or case | done, with two library rules | Only comments name cases. `gc/runtime/PoolWorkers` names Jetty's `QueuedThreadPool.startThread`. The wire rule and scope growth name `.protobuf.` (the wire rule also `.protobuf.RpcController`). |
| VM code naming a system | done | Only comments. Library lists are hard-coded: logging and crypto are muted, commons-lang 2 and Spring `StringUtils` are modeled, two Jackson classes are muted. |
| Per-case switches | not done | `causynth_scope_growth_budget=0` in every named case; per-case `WIRE_FLOW` rows; hand roots and target rewrites in the trees; `region_path_max_tasks=128` for 11741. |
| DOOR rows once per system | not done | The same rows are copied into every case's `communication-mappings.jsonl`. |
| Dead or fallback code | not done | See "Fallbacks and dead code" below. |

## Per-system surface

What a system costs today, outside the general engine.

| part | HDFS | Solr 8.11 |
| --- | --- | --- |
| code in this repository | the Hadoop shim `src/shim/java/org/apache/hadoop/ipc/{CausynthMessagePropagation,CausynthSymbolicSource}` (a `hadoop-shim` jar) | none; the tree calls `gc/runtime/MessageDoors` directly |
| harness | `experiments/hadoop/{system.sh,build.sh,classpath.py,javac8-filter-crc32c.sh}`; `system.sh` also holds the block-key family scope `blockkey_scope` of the named cases, the ad-hoc starting scope `system_mapping_scope` (the classes the ad-hoc DOOR and WIRE_FLOW rows name) and `system_cluster_class` | `experiments/solr/{system.sh,build.sh,classpath.py}`; `system.sh` holds `system_mapping_scope` (the DOOR classes), `solr_state_scope`, `system_cluster_class`, a fixed test seed, and `-Dcausynth.cluster.automatic=true` |
| DOOR rows | `HADOOP_IPC` REQUEST and RESPONSE, `HDFS_SASL` REQUEST; ad-hoc adds `HDFS_DATA_TRANSFER` SEND | `SOLR_HTTP` REQUEST and RESPONSE, `SOLR_ZK` SET_DATA and CREATE, in `solr-adhoc` only; solr-18406 and solr-18413 have no doors |
| tree: transport | IPC `Client`/`Server` and `RpcHeader.proto` fields; SASL `DataTransferSaslUtil`/`SaslDataTransferClient` and `datatransfer.proto` fields | `CausynthHttp` with calls in `HttpSolrClient`, `Http2SolrClient`, `ConcurrentUpdateHttp2SolrClient`, `SolrDispatchFilter`, `HttpSolrCall`; `SolrZkClient` store and notify hooks |
| tree: daemon ticks | `beginTick`/`endTick` in `KeyManager`, `HeartbeatManager`, `BPServiceActor`, `DataXceiver` | `Overseer`, `OverseerTaskProcessor`, `ReplicationHandler` (with `vacant`) |
| tree: roots | `CausynthSymbolicSource.symbolize`: 6 hooks in `BlockTokenSecretManager`, 1 in `SnapshotManager` (hdfs-17960's config root) | none |
| tree: cluster and bounds | `CausynthCluster` (with automatic mode), `MiniDFSCluster` hooks, timeouts in `CausynthCluster.configure`, `pinBlockKeys` copies in the workloads | `CausynthSolrCluster`, `MiniSolrCloudCluster`, `SolrCloudTestCase`, `CausynthBounds` and its uses; `ClusterState` keeps live nodes in a `TreeSet`; Overseer batching off in automatic mode |
| tree: targets | each named case's target throw carries `@CausynthExceptionTarget("<case ids>")` (`BlockTokenSecretManager.retrieveDataEncryptionKey` for the seven block-key cases, `FSImageFormatPBSnapshot` for hdfs-17960, whose `Preconditions.checkState` is spelled as an if/throw); the cases' specs are derived from it (`tools/lib/annotated.py`) and a sweep's finding there is a known bug (`findings.py --annotated`); no engine code reads it, and ad-hoc checks carry none (`target.yaml` names class and line). hdfs-17897's fix is reverted (e23df4c4b84) | the same (Solr trees not yet unified). SOLR-18413 also turned a `getCollection` call in `DistributedZkUpdateProcessor` into `getCollectionOrNull` plus a local throw, and turned `SliceMutator`'s `expireAt` into a `Long.parseLong`/`String.valueOf` round trip so that its `WIRE_FLOW` rows have capture sites. |
| branches | `gc/hdfs-unified` (`~/hadoop-hdfs-unified`): one adapter, every named case and the ad-hoc experiment; `gc/hdfs-11741` apart | `gc/solr`, `gc/solr-18406`, `gc/solr-18413`, `gc/solr-adhoc`; the Overseer `consumed` call exists only on the three derived branches |

## Open defects

Correctness:

1. Flip queries keep a refused construct in a decision or prefix term as a free
   `unsupported__*` constant, with no gap (`gc/explore/FlipQuery#statedTerm`; FlipQuery opens
   no refusal frame). A refused arm is dropped by name. A query can therefore ask for a world no
   replay can plant.
3. Valuations are cut at `compose_max_valuations` with no gap. Only single and pair moves are
   tried, and integral values are enumerated from the domain minimum (`gc/compose/Composer`).
   No `INCONCLUSIVE_BOUNDED` claim exists.
4. `gc/explore/FlipQuery`: a CLOCK with no reading gets the window `[0, Long.MAX]`.
5. `==` and `!=` between a boxed container cell and a primitive are not unboxed. They are
   refused as `BinarySortConflict` (`gc/compose/SmtLowering`).
6. VM: `String.toCharArray`/`getBytes`/`getChars`, `new String(bytes)` and a native method with a
   symbolic argument lose the expression with no trace; an `Unsafe` get of a tracked location is not
   a versioned read.
7. VM: implicit exceptions (NPE, AIOOBE, division by zero, a failed cast) and `instanceof` are
   never symbolic branch outcomes.
28. `gc/runtime/MessageDoors#stored` files what a store's write carried after
    `CausynthTraceRecorder#outboundExchange` observed its SEND, and the schedule may run the
    version's reader from that SEND on: `consumed` or `fetched` can find nothing, and the
    delivery pairs with no export (SOLR-18413 r5's seed, the Overseer's queue item).
29. No read row states Java null: in hdfs-17899-bug2 r4's seed none of 333 reference reads
    states `N`, though the VM serializes a null it returned as `concreteValue: null`
    (`ReturnedValue::NULL_REFERENCE`). A read of a null at an `INITIAL` version (bug2's
    `KeyManager.encryptionKey`) then has no pin and is refused. `RowCodec#toLine` (a default
    `Gson`) also drops null members from `expressions.jsonl`.
30. VM: a container query (a `MAP_STATE` read: `get`, an iterator) states no value it returned, and
    `toString` of an object the VM names (an enum constant) is an `OpStrExpression` over its symbol
    with no string (`NON_INTEGRAL_TERM`): a read whose join rests on either can be neither joined
    nor pinned.
31. `gc/smt/Arms#concurrent` orders an anchor-chain ancestor occurrence before all of its
    descendant, so the writes of a task are no alternative arm for its starter's later reads.

Scale and robustness:

9. One BLOCKING row invariant in any focused session fails the campaign at the wave gate. The
   offending session is not withdrawn.
10. A truncated closure is BLOCKING (`gc/explore/ExploreMain#plan`). It is DIAGNOSTIC only
    when `region_path_stop_at_fatal` is set and a replay has already observed the fatal.
11. Every obligation solver reads the whole corpus (`gc/explore/ObligationSolverMain`).
12. The seed recording has no wall-clock bound; only the case budget ends it.
13. VM: every expression is kept until the session closes, under one global mutex.
32. COMPOSE lowers and states a message family once per path that binds it
    (`gc/compose/ComposedFamilies#messageFamily`): hdfs-11741 r3's 47 paths carry 7 MB of family
    text per query, each arm body up to twice.

Fallbacks and dead code:

14. `gc/explore/ClosurePlanner#holds` falls back to region-id equality when the scope map knows
    no method set.
15. `gc/plan/SelectorResolution#resolve` returns a degraded `unresolved` address instead of
    refusing.
16. `gc/runtime/ScheduleLog#timeoutMillis` silently takes the default for a malformed value.
17. VM dead code:
    - six natives serve only the smoke tests: `getPathCondition`, `trackContainerExpression`,
      `getSharedFieldVersions`, `getSharedElementVersions`, `getSharedMapVersions`,
      `getConcolicRegionSummary`;
    - nothing runs `causynth_smoke_test.sh`.
18. `gc/compose/SmtLowering`: the `PlaceholderExpression` dispatch has no producer.

Harness and declarations:

21. `src/test/resources/external-callers.txt` lists APIs no tree calls, and omits
    `MessageDoors`, which the Solr trees call.

Stale artifacts:

27. `gc/runtime/RuntimeRegionPlanner` drops a recorded region entry whose method no candidate
    skeleton roots, with no gap: a recording joined with static artifacts of another build (a
    lambda class named otherwise, a shifted unit) loses its activations and folds silently.
