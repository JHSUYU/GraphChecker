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
`/bigtemp/vnr3ne/gc-out/accept-<round>-<case>/`. Rounds `r7` (main `d0acb339a`), `r8` (main
`8820c3129`), `r9` (main `a53174bf1`). HEAD (`f3b31968a`) adds W5, the ad-hoc WP1/WP5.C/WP2
tools and later fixes on top; no full round has run on HEAD itself.

| case | run | verdict | mechanism / blocker |
| --- | --- | --- | --- |
| hdfs-17897 | `r7` | PASS | MARKER_FLIPPED, IPC request door (`REGION.763d087e`) |
| hdfs-17899-bug1, bug3 | `r7` | PASS | MARKER_FLIPPED, IPC request door |
| hdfs-17899-bug2 | `r8` | PASS | MARKER_FLIPPED, IPC response door (`REGION.9ffdee3d`) |
| hdfs-17960 | `r8` | PASS | MARKER_FLIPPED, `HDFS.CONFIG.SNAPSHOT_DELETION_ORDERED=false`, confirmed |
| hdfs-17967-pathA, B, C | `r7` | PASS | MARKER_FLIPPED, IPC request door |
| hdfs-11741 | `r8` | FAIL | CLOCK_SKEW (NameNode and DataNode clocks, `polarityDecides`) but 22 BLOCKING gaps: 18 EXPLORE `TOPOLOGY_DIVERGENCE` (`SlotTable#contradictsOrder` orders by the anchor chain), 3 PLAN `OCCURRENCE_ADDRESS_SHARED` (a pool task inherits no frames), 1 COMPOSE `UNSTATED_VALUE` (an export stating no expression). Fixed off main (README §0.3). |
| solr-18406 | `r7` | FAIL | its one anchor path is UNSAT with every root free. Fixed off main: a run of that branch (`accept-a37f4-solr-18406`) PASSES with CLOCK_SKEW, confirmed. |
| solr-18413 | `r9` | FAIL | the `isExpired#u6` flip is SAT and its replay observes the fatal ("Could not find collection") and is ADMITTED, but IMPORT invariant 9 stops the campaign: that replay's target row states no `phiTerm`, since the fatal condition is concrete there. |

So HDFS stands at 8 of 9 on main. The ad-hoc checks have found no new bug; the only confirmed
ad-hoc witnesses ever were two CLOCK_SKEWs on token-expiry checks, judged to be HDFS's clock-sync
assumption.

## R1. Symbols come automatically from the fatal slice

| capability | status | where | missing |
| --- | --- | --- | --- |
| Backward data slice from the declared throw across methods (arguments, returns, callers, CHA dispatch) and field writers | done | `gc/causynth/SeedBackwardStaticAnalyzer` | Application classes only. The field jump is instance-insensitive. |
| Control dependence inside a method | done | `gc/causynth/SiteControlDependence` | The CFG is a `BriefUnitGraph`, so exception edges are ignored and a catch handler a fault leads to has no guard. The slice uses may-reach; the scope map's guards use post-dominance: two relations. |
| Control dependence across methods, threads and the wire | partial | `SeedBackwardStaticAnalyzer` (callers of field writers, constant stores up to 3 calls up) | Nothing across a thread start, an executor submit or a message. |
| Library-typed state (the receiver of a non-application call) | not done | `SeedBackwardStaticAnalyzer#localValueUses`, `#isValueLikeLibraryInvoke` | `x = lib.m(k)` depends on `k` only, except modeled containers, String/StringBuilder, unboxing and structural accessors. State behind a `ConcurrentMap`, `NavigableMap`, `AtomicBoolean` or cache never enters the slice. |
| CLOCK roots by category | done | `gc/causynth/RootCatalog#clockTicks`, `#wrapsAClock` | Only the JVM clocks and zero-argument int/long wrappers under constant arithmetic, found on `call_return` edges. Not `java.time`, a clock read through a field, or a delegate outside the scope. |
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
| Composer merges both sides (MESSAGE families) | done | `gc/compose/ComposedFamilies`; `gc/smt/Arms` | Only arms of the same interaction slot, from sessions of compatible worlds. An unpaired attach refuses its path. |
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
| Select checks by the engine's own static slice; declare their targets | done | `run_engine.sh` `slice` (SEED's static half, scope grown, no workload); `tools/adhoc/select.py declare` (every reached check a sweep can run, skipping, and naming on stderr, a timeout's check, a workload whose test failed under coverage or starts no node, a moved line), `slice.sh` (one slice per check on the lifts, `$GC_OUT/static/<key>/<check>/`), `score.py` (the roots the slice reaches back from the throw's branches: clock, fault, `READ`, cross-region store, wire crossing; keep = a root within 4 edges, calibrated on 260 h4/q* verdicts), `select.py rank` (`selected.jsonl`, three per class, a 5% calibration tail of dropped checks), `targets.py`; `gc/causynth/ExceptionTargetLineResolver` | The ~2000 reached checks are not yet all sliced (70-100 s and 3.2 GB RSS each). keep is a weak filter: of the checks it keeps, 66% still had their anchor decided concretely (88% of those it drops). The score saturates beyond keep. A door counts only when a store's method calls it within three calls of the slice: the IPC doors the block-key witnesses flip show only as a wire crossing. A declared config root (hdfs-17960) is no root kind the score names. A throw in a lambda body or an anonymous class resolves, but a slice that starts in a `lambda$…` body stops at its captured arguments (no `invokedynamic` call edge). |
| Fan out over ten lifts under a memory gate | done | `tools/adhoc/sweep.sh`, `fanout.sh` (a job's `NEED_MB`, resume over `<n>.exit`); `tools/lib/gc-env.sh` (`GC_OUT`, `CAUSYNTH_HOST_LEDGER`, `LIFTS`); `run_engine.sh` `campaign_host_try_start` (need and ramp per row), `campaign_head_charged` (a head's engine JVMs and replays), `campaign_worker_slot_hosts` (rotated per wave); no start leaves a host more than `CAUSYNTH_HOST_MAX_USED_PCT` (70) percent full (the reserve is 30 % of its `MemTotal`), and `/bigtemp/vnr3ne/bin/pick-lift.sh` (`onlift.sh`, `offline-ab.sh`) places by the same ceiling | A charge is the stated heap, not the measured RSS, and it lapses after the ramp: a JVM that grows past it later is seen only in `MemAvailable`. `offline-ab.sh` places through `pick-lift.sh`, not the ledger, so a gate's case and a campaign's starts do not see each other's ramps. Every obligation solver loads the whole corpus (5-7 GB RSS; defect 11). |
| Disk and quota gate | done | `experiments/accept/accept.sh` `acc_free_gb`: `MIN_FREE_GB` free on the filesystem `OUT` is written to, and a refused 1 MB write there reads as 0 | — |
| Time bounds | partial | case budget 5400 s (`sweep.sh`); obligation replay 2400 s (`replay_timeout_s`); seed replay `seed_replay_time_factor` (40) × the recorded workload's time, at least `replay_timeout_s` (`run_engine.sh` `campaign_session_replay`) | The seed recording has no wall-clock bound of its own; only the case budget ends it. |
| Replay schedule stalls | done | `gc/runtime/ScheduleLog#watchdogLocked`, `#computingLocked` | The engine's own threads (`causynth-*`) never defer a give-up, and a let-go no longer restarts the stall's clock: a never-coming event costs a timeout plus a 2 s grace when no workload thread computes, and at most eight timeouts plus the grace when one does (s49: 17 stalls of 120 s, two per episode). Every workload thread's CPU counts, because which thread owes a slot cannot be seen between its events. |
| Replay polling past the recording | done | `ScheduleLog#waitsAtLocked`, `gc/runtime/ClockLoops` | While the prefix stands, a loop past its recorded count polls once per move of the order (s49: 6862 such WAKEs spun free on the wall clock). A loop that reads a CLOCK root stays free; the check is by method on the waiting stack, so a clock read in a callee that returned before the wait is missed. Past the cut such polls still run free. |
| Stop at a first fatal | partial | `region_path_stop_at_fatal` (`gc/explore/ExploreMain`) | Only `solr-adhoc` sets it. |
| One recording per workload for several checks | partial (pre-screen) | `run_engine.sh` `record` (one recording woven with every target's skeletons merged by region and every target's grown scope, `campaign_union_static`; bounded by `record_timeout_s`; `runtime/record-summary.json`); `runtime.CausynthTraceRecorder` (the trace read once, each `--target` aggregated on its own slice and skeletons, a refusal its own `NOT_IN_WINDOW`, `TARGET_BRANCH_NOT_OBSERVED`, `POLICY_ABSENT`, `NO_REGION` or `ERROR`, with `fatalArmObserved`); batch cases `B<n>` (`batches.tsv`, `targets/B<n>.yaml`); `tools/adhoc/cover.py` (a greedy cover of the selected checks by their tests, at most 16 per recording, two tests per check; then the campaign cases from the activated pairs), `prescreen.sh` | A campaign still repeats SEED, INSTRUMENT and the seed replay per check (WP3). The pre-screen's occurrence addresses carry the other targets' root frames, so they are not a solo campaign's. |
| Triage | partial | `tools/adhoc/triage.py`: CONFIRMED, REFUTED (`SAT_UNCONFIRMED`, with the confirmation's reason), NO_WITNESS, STOPPED (with the reason its logs state), DEAD (no lift runs it any more), RUNNING, PENDING | `UNSAT_CLOSED` is folded into NO_WITNESS. |
| Dedupe and rank findings by mechanism | done | `tools/adhoc/findings.py` (signature: the check's TARGET_SITE, the finding kind, and per moved root its kind -- a fault door's marker is FAULT --, site method, callee, node role, causal context and a clock's skew bucket; read from `result.json`, the plan's input action and the selected session's `roots.jsonl`, all kept by PRUNE); `$GC_OUT/findings/ledger.jsonl` (new, known, dismissed by `dismissed.tsv`) | The weight's native reproduction factor waits for WP5.D. The mediated bonus reads `score.json` by TARGET_SITE, so the static root must be the sweep's own build; the IPC door roots of the block-key witnesses are not in their slices (only as a wire crossing), so they get no bonus. A CLOCK root row from before the `clockNanos` contract is refused by name. |
| Automatic cluster as a workload | partial (tree patches) | HDFS `CausynthCluster` automatic mode on `hadoop-hdfs-17967-c` only; Solr `CausynthSolrCluster` | Real-time bounds are patched per system; upstream HDFS workloads are limited to one DataNode (`ThreadLocalRandom`). |

## R5. Correct .smt for the Solr cases; the nine HDFS cases keep passing

See Acceptance above. What remains (the branches are in README §0.3):

- hdfs-11741: the 22 blockers are fixed off main; its three NameNode clocks that move only through
  the `clock_order` constraint may still fail the cone gate.
- SOLR-18406: reference-carried container state and the `ConcurrentHashMap` model are on main
  (R3); the clock planting fixes that make it pass are off main.
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
| tree: roots | `CausynthSymbolicSource.symbolize`: 6 hooks in `BlockTokenSecretManager` of every block-key tree, 1 in 17960's `SnapshotManager` | none |
| tree: cluster and bounds | `CausynthCluster` (automatic mode on `hadoop-hdfs-17967-c` only), `MiniDFSCluster` hooks, timeouts in `CausynthCluster.configure`, `pinBlockKeys` copies in the workloads | `CausynthSolrCluster`, `MiniSolrCloudCluster`, `SolrCloudTestCase`, `CausynthBounds` and its uses; `ClusterState` keeps live nodes in a `TreeSet`; Overseer batching off in automatic mode |
| tree: targets | none needed: `target.yaml` names the class and line. The trees still carry `@CausynthExceptionTarget` on each target `throw` (one per case; one per ad-hoc check on `hadoop-hdfs-17967-c`), read by no engine code | the same. SOLR-18413 also turned a `getCollection` call in `DistributedZkUpdateProcessor` into `getCollectionOrNull` plus a local throw, and turned `SliceMutator`'s `expireAt` into a `Long.parseLong`/`String.valueOf` round trip so that its `WIRE_FLOW` rows have capture sites. |
| branches | one `gc/<case>` branch per case, each carrying the whole adapter | `gc/solr`, `gc/solr-18406`, `gc/solr-18413`, `gc/solr-adhoc`; the Overseer `consumed` call exists only on the three derived branches |

## Open defects

Correctness:

1. Flip queries keep a refused construct in a decision or prefix term as a free
   `unsupported__*` constant, with no gap (`gc/explore/FlipQuery#statedTerm`; FlipQuery opens
   no refusal frame). A refused arm is dropped by name. A query can therefore ask for a world no
   replay can plant.
2. A flip model that assigns no root is still dispatched (`gc/explore/ObligationFactory`), and
   its replay is always NOT_ADMITTED.
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

Scale and robustness:

8. One remote obligation worker that exits nonzero fails the wave and the campaign
   (`run_engine.sh`).
9. One BLOCKING row invariant in any focused session fails the campaign at the wave gate. The
   offending session is not withdrawn.
10. A truncated closure is BLOCKING (`gc/explore/ExploreMain#plan`). It is DIAGNOSTIC only
    when `region_path_stop_at_fatal` is set and a replay has already observed the fatal.
11. Every obligation solver reads the whole corpus (`gc/explore/ObligationSolverMain`).
12. The seed recording has no wall-clock bound; only the case budget ends it.
13. VM: every expression is kept until the session closes, under one global mutex.

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

20. `experiments/hbase/token-key-roll-concolic/workflow.properties` uses a key `run_engine.sh`
    refuses, so that case cannot run.
21. `src/test/resources/external-callers.txt` lists APIs no tree calls, and omits
    `MessageDoors`, which the Solr trees call.
23. `tools/analysis/confirmrun.sh` calls `campaign_confirm_decide`, which `run_engine.sh` no
    longer has: the decision is `explore.ConfirmMain --sessions`, which also needs the claim.

Stale artifacts:

27. `gc/runtime/RuntimeRegionPlanner` drops a recorded region entry whose method no candidate
    skeleton roots, with no gap: a recording joined with static artifacts of another build (a
    lambda class named otherwise, a shifted unit) loses its activations and folds silently.
