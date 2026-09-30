# Symbol scope: what is symbolic, and from where

SEED computes one static slice `S` backwards from the annotated throw and publishes, per site of
`S`, what a replay does there: mint a root, observe shared state, export or attach a wire value, or
nothing. Java paths below are under `src/main/java/edu/uva/liftlab/graphchecker/`.

Three things are kept apart:

- a **root** is a fresh symbol the replay mints (a clock reading, a fault marker, a configured
  source). Only roots add freedom.
- a value is **symbolic by propagation** when the VM's shadow carries an upstream root's expression.
  The VM propagates through every bytecode a region's thread interprets, whatever the analysis
  scope (VM.md); the slice decides only where roots, tracked reads and ports are.
- a **tracked** location is one the VM versions from its first observed access, so COMPOSE can
  re-pair a read of it with another writer (a STATE family).

## 1. The rule

| where a value comes from | what it is | bound by |
|---|---|---|
| **F1** the environment: a clock read, a door fault, a configured source hook (§4) | ROOT | its domain: a marker both values, a configured source its `root-domains.jsonl` row (none: pinned), a clock its window (`contract/RootKind`, `contract/RootDomain`) |
| **F2** a read of shared state another occurrence writes (§5) | TRACKED READ, or a READ placeholder where the accessor is unwoven | the version it observed, and every attested HB-concurrent writer occurrence of the same session (`smt/Arms#stateArms`) |
| **F3** a message leaf that crosses a process (§6) | WIRE ATTACH, a fresh `v_H` per primitive leaf | the producer's export, paired within the run (message families) |
| **F4** a return or parameter from code outside the analysis scope | grow the scope (§2.4); what stays outside has no root, tracked read or port, and is symbolic only by propagation | its inputs' expressions, else the recorded value |
| a read of state from before the window | the INITIAL version of its log | pinned to the recorded value |

A value no rule makes symbolic is concrete: `plan/ConcolicScheduler.SymbolicInputSelection` marks
every other proposed input `CONCRETE` (`UNDECLARED_SYMBOLIC_INPUT`), and its expression, if any,
still rides with the value. A root with no domain is pinned (`RootDomain`). A read COMPOSE cannot
bind is pinned to its recorded value or refused as `UNSTATED_VALUE` (`compose/Composer`).

## 2. The slice `S`, and its scope

`causynth/SeedBackwardStaticAnalyzer#analyze`, run by `causynth/CausynthPipeline#analyze` after
`DoorWeave.apply()` (§4.2), so every pass sees the woven doors as program text.

### 2.1 Seeds

- The annotated throw (`@CausynthExceptionTarget`, one Jimple throw or the analysis refuses): the
  thrown value (`exception_throw`) and the operands of every branch from which the throw is
  reachable (`exception_guard`).
- Every capture of every declared WIRE_FLOW port (`seedDeclaredWireFlows`), whether or not the throw
  needs it.
- Every call of `Debug.makeSymbolicBoolean` (`seedExplicitFaultEntries`): its result cell and the
  guards of that call.

### 2.2 Propagation rules

The worklist (`runWorklist`, `processMethod`) walks definitions backwards:

- **Locals, arguments, returns** into callees whose body is analysed: a concrete method of a
  non-abstract application class that is not a structural field accessor (`isExpandableMethod`).
  Callers of a demanded formal or of a demanded `this`, constructor callers, and CHA dispatch to the
  application implementations of an interface or abstract call (`processDispatchInvoke`; owners in
  `java.`, `javax.`, `com.google.`, `org.slf4j.` are not dispatched).
- **Field jump**: a demanded read of an application field demands every write of that field in the
  scope (`expandFieldWriters`). Field-level, not per object.
- **Control dependence**: a demanded definition demands the operands of every branch from which it
  is reachable by a proper subset of the branch's successors (`demandControllingGuards`,
  `SiteControlDependence.MethodGuards#reaching`), published as `guard_dependency` edges.
- **Constant stores**: a store of a constant carries no data, so the guards of the calls into the
  storing method are demanded too, up to three calls up, dispatch included
  (`expandStoreCallerGuards`, `STORE_CALLER_DEPTH`).
- **Field reads**: a demanded `x = b.f` demands `f` (`field_read`, then the field jump) and `b`,
  the object it reads from (`local_def_use`: the base is a use of the read), as an accessor's
  receiver (`accessor_receiver`) and a dispatched call's (`dispatch_receiver`) are. A reference
  read only to reach a projection (SOLR-18406's `latestCommit`, whose generation the throw
  compares) is therefore a cell a branch decides through (§5.1).
- **Library calls**: the result of a non-application call depends on its arguments only; its
  receiver is dropped (`localValueUses`). Exceptions: `String`, `StringBuilder`,
  `StringBuffer` and every wrapper's unboxing accessor (`smt/JavaPrimitiveBoxing#unboxing`,
  `Boolean.booleanValue` included) keep the receiver (`isValueLikeLibraryInvoke`); a JDK
  atomic's `get()` is an accessor of its `value` (`AtomicBoolean.get()` is `value != 0`), read
  off a table rather than its body (`plan/SharedFieldFlow#atomicRead`,
  `StructuralFieldAccessorProof#atomicField`); and a container query depends on receiver and
  arguments (`processSemanticContainerOperation`, `container_receiver`, `container_argument`).
- **Containers, by interface** (`smt/JavaContainerTypes`): a call's contract is its receiver
  type's interface's -- `Map` (`ConcurrentMap`, `SortedMap`, `NavigableMap` alike), `Set`
  (`NavigableSet`), `List`, `Queue`, `Deque`, `Iterator`, `Map.Entry` -- read off the Soot
  hierarchy of a library class, else a fixed list of JDK classes (`ConcurrentHashMap`, `TreeMap`,
  `ConcurrentSkipListMap`, `LinkedList`, the concurrent queues, ...). A call is named by its name
  and parameters, never its return type, which an implementation narrows. A *query* (`get`,
  `getOrDefault`, `containsKey`, `computeIfAbsent`, `floorKey`, a view, `poll`, ...) depends on its
  receiver; a *mutation* (`put`, `merge`, `putIfAbsent`, a view's `removeIf`, `push`, ...)
  demands its arguments into its receiver (`container_mutation_argument`) and, through a field
  alias, is a `field_mutation` of that field. An application class's calls run the body the slice
  follows: it states no contract. Whether the VM models a class is decided at run time, never here.
- **Publication** (`publishMutation`): a mutation of the container a local `L` holds shapes the
  referent every later store of `L` (or of a copy of it, before `L` is redefined) publishes into
  a field `F`, and, one call up, the referent a method returns into each field its callers store
  the result into. Each such `F` gets a `container_publication` edge `L -> F` at the mutation
  (`publishedFrom: L`): the map's write site of `F` there (§5.1). SOLR-18406's
  `updateKnownCommitPoints` puts each commit whose `!wrapper.isDeleted()` holds into a fresh map,
  then stores the map into `knownCommits`.
- **Arrays**: element cells stay in the slice; an index never turns symbolic
  (`processArrayAccesses`). Literals are ignored.

### 2.3 What SEED publishes

`causynth/StaticProgram` is the in-memory catalog (edges, selected methods, region skeletons,
communication call sites, retained loops). `causynth/CausynthArtifactWriter` writes, into the
causynth output directory:

| file | content |
|---|---|
| `candidate_dataflow_edges.jsonl.gz` | the slice's edges (`kind`, `fromCell`, `toCell`, `method`, `unitIndex`, `invoke`, ...) |
| `region_skeletons.jsonl.gz` | the regions built around execution-context entries (`causynth/SymbolicRegionPlanner`), with their ports and retained loops |
| `communication_gaps.jsonl.gz` | ports or loops the planner could not place |
| `static_scope_map.jsonl` | §3; built before any hook is woven, over the door-woven bodies (§4.2), so site ids are the unit indices every pass and every replay decides at |
| `scope_frontier.jsonl` | §2.4 |

These files are a function of the scope's classes, the same bytes on every host and run
(`tools/regress/offline-ab.sh` gates on it):

- Soot runs on one thread over the classes by name (`GraphCheckerMain#orderClassesByName`), not
  in the order the filesystem lists the process dirs.
- A lambda class is named by its content (`GraphCheckerMain`'s `LambdaClassNames`), not by Soot's
  run-wide counter.
- Soot's `jb.sils`, which gives each use of a constant-defined local its own copy, takes the uses
  in body order (`SharedInitializationSplitter`), not in identity-hash order.
- A body's locals are numbered by type and first definition (`jb.lns` `sort-locals`).
- Hierarchy answers (dispatch targets, subclasses) are taken by signature or name.
- The worklist runs to a fixed point: a caller whose actual a callee's demand reached, or a method
  whose field effects or constant stores grew, is processed again (`markDirty`).
- Edges are numbered `DF.<n>` and written in content order (method, unit, kind, ends), not in the
  order the worklist found them.

### 2.4 Scope growth

The case's `scope=(...)` class list is where `S` starts. `run_engine.sh
campaign_analyze_grown_scope` reruns the static pass until nothing is added or the budget is spent:

1. `plan/ScopeFrontier#rows` lists where `S` stops, each row with its `distance` (edges from its
   cell back to the throw's sinks), nearest first:
   - `CALLEE`: a callee whose return `S` demands but whose body is not analysed (and is no clock);
   - `FIELD`: a field `S` reads or stores;
   - `FORMAL`: a method whose primitive or `String` formal `S` demands only through a field. A
     formal reached without a field in between is on the target's own call chain and is never a
     row: growing its callers would move the region root and with it the target's identity.
2. `plan/ScopeGrowth` resolves each row over the classes of `causynth_lineage_roots`:
   - `CALLEE`: the class whose body runs it (for an abstract method, the class each implementation
     inherits it from), unless that body only loads constants;
   - `FIELD`: its owner and, unless the field is private or final, every class storing it; a
     static final field is a constant and grows nothing;
   - `FORMAL`: every class calling the method;
   - never a generated protobuf class (a supertype in `*.protobuf.*`).
   Each class taken is copied into `<causynth_output_dir>/scope-classes/` and listed in `GROWN`
   (`class`, `kind`, `signature`, `distance`) until `causynth_scope_growth_budget` classes
   (default 24; `0` disables growth) are grown.
3. The grown directory joins every later pass as `-Dcausynth.process.dirs`: one application scope.

Only classes under the lineage roots are indexed, so nothing else (the JDK, a library jar) is
ever grown.

## 3. The static scope map

`plan/StaticScopeMap` builds `static_scope_map.jsonl` (`#sites`, `#rows`) from the edges and the
region skeletons. One row per (role, region, site); every row states `schemaVersion` 1,
`kind: STATIC_SCOPE_SITE`, `role`, `regionId`, `siteId` (`<method>#u<unitIndex>`), `vmSite` (the
method as the VM spells it, the join with recorded endpoints), `cell`, `carrier`, `portId`,
`guards` and `guardOutcomes`.

| role | one row per | extra members |
|---|---|---|
| `TARGET_SITE` | the annotated throw | `chain`: the guards of its guards within the method, each on its arm toward the throw (`Guards#chainOf`) |
| `ROOT_SITE` | a call site whose `<callee>.return` defines a local of its method | `local` |
| `DECLARED_SITE` | a value entering from outside the slice's text: an `ACCESSOR_RETURN` (a structural accessor; cell = the field) or a `CALL_RETURN` (a clock, a fault marker) | `declaredKind`, `edgeId`, `dependencyCell`, `javaType` (primitive only), `implementationMethod`, `inputKind` (`CLOCK`, `FAULT`, `READ`, or absent), `clockNanos` |
| `READ_SITE` | a read of a tracked cell (§5.1) | `trackedKind` (`VALUE`, `REFERENCE`), `static` (a static field) |
| `WRITE_SITE` | a store or container mutation into a field `S` names | `declaredCallee`, `callers`, `publishedFrom` (the local a publication mutates, §2.2) |
| `EXPORT_SITE` | the producer capture of a port (OUT side only) | `portId` |

**Guards** (`causynth/SiteControlDependence`): site `t` is control-dependent on branch `b` when
some successor of `b` is post-dominated by `t` and `b` is not; the outcome names the arm that
reaches `t`. The CFG has no exception edges (`BriefUnitGraph`). A `WRITE_SITE` also carries the
guards of the calls into its method, up to three calls up (`Guards#callsInto`, `CALL_DEPTH`), and
those callers (`Guards#callersOf`). A guard that tests a helper's constant return names the helper
branch that decides it (`causynth/BooleanReturns`, `guardDeciders`).

The slice (§2.2) and the map use two relations: the slice widens by may-reach, the map's guards
are post-dominance.

Readers: `ConcolicScheduler` (admission, observed sites), `runtime/GuardedStoreSites` (§5.3),
`explore/ClosurePlanner` (static producers of a port, `#exportsOf`; static candidate writers of a
demanded read, §5.5), `RuntimeSelectedRegionFinalizer` (root admission, §4.4). For COMPOSE the map
states each reference store's construction guards (`#constructionGuards`, §5.6).

## 4. Roots (F1)

### 4.1 Clocks

`causynth/RootCatalog#clockTicks`, over the slice's `call_return` edges. A clock is
`System.currentTimeMillis()` or `System.nanoTime()`, or a method with no parameter, returning
`int` or `long`, each of whose returns is a clock value under constant arithmetic (casts, negation,
binary operations with constants), each local defined once, followed up to four wrappers deep
(`MAX_DEPTH`). The clock's tick in nanoseconds is read off the arithmetic (`nanoTime / 1000000`
ticks in milliseconds); a wrapper with no readable scale ticks in milliseconds.

A `DECLARED_SITE` with `inputKind: CLOCK` is published for a `call_return` of a clock that no
region holds as its own method. A `CLOCK` root's value in a replay is the reading plus a skew the
obligation states (`FocusedReplay.clockSkew`).

### 4.2 Fault markers

A `DOOR` row of the communication mapping (`causynth/DoorWeave`):

```json
{"schemaVersion": 1, "kind": "DOOR", "transport": "HADOOP_IPC", "direction": "REQUEST",
 "method": "<...Client$Connection: void sendRpcRequest(...)>",
 "after": "<...CausynthMessagePropagation: ...Outbound outbound(...)>",
 "faults": ["java.io.IOException", "org.apache.hadoop.net.ConnectTimeoutException"]}
```

At the first call of `after` (or before the first call of `before`) in `method`, the weave inserts,
per fault kind in row order, `if (Debug.makeSymbolicBoolean(name)) throw new Kind("symbolic
<name>")`, the false arm falling to the next marker. `name` is `FAULT:<TRANSPORT>:<DIRECTION>` for
`java.io.IOException` and `FAULT:<TRANSPORT>:<DIRECTION>:<SimpleName>` otherwise. A method, call or
exception class that does not resolve is refused by name (`DOOR_METHOD_UNAVAILABLE`,
`DOOR_SITE_UNAVAILABLE`, `DOOR_FAULT_KIND_UNAVAILABLE`). A kind is an environment failure the
transport can raise and a caller tells apart (a retry policy fails over on one and retries
another); a semantic server exception is never a kind, it must come from the causal chain. The
weave runs before any analysis (`CausynthPipeline#run`), so every pass numbers units over the same
woven body and site ids agree across passes; they differ from the unwoven method's.

A `FAULT:` marker is a `DECLARED_SITE` (`inputKind: FAULT`) iff its transport has a DOOR row
(`StaticScopeMap#declaredFault`, `WireFlowCatalog#declaredTransports`); a marker whose name does
not start with `FAULT:` is the workload's own and always declared. The recorded polarity is
`false`. How fault decisions become flip sites is IDENTITY.md §7.

### 4.3 Configured sources

A tree calls `CausynthSymbolicSource.symbolize(String sourceId, Object owner, String
fieldSignature)` (the Hadoop copy is `src/shim/java/org/apache/hadoop/ipc/CausynthSymbolicSource`).
`causynth/StaticSymbolicSourceDiscovery` finds the call by class simple name and signature and
attaches one declaration per source to every region that can run it (one hook site per source
per region, else refused). At the hook, `runtime/RootMint#configuredSource` mints one symbol per
source on the owner's primitive instance field, keeps a propagated expression instead when the
field already carries one (`reused`), and plants the value the obligation asks for. Its domain is
the `root-domains.jsonl` row for `sourceId` (absolute or `+k`/`-k` from the recording); without a
row it is pinned.

### 4.4 Admission

`plan/ConcolicScheduler.SymbolicInputSelection#decide` gives each proposed input one verdict:

| input | verdict |
|---|---|
| a clock's return, a READ placeholder's own site, a `FAULT` marker | declared root: the replay mints (`DECLARED_SYMBOLIC_ROOT`; a clock also `DECLARED_WALL_CLOCK` = its tick) |
| a field a configured-source hook of the region mints | `CONCRETE`, `CONFIGURED_SYMBOLIC_SOURCE_FIELD_OWNED` (the hook mints) |
| a declared communication port (`COMMUNICATION_SITE_PORT`) | tracked, never minted (the attach installs the producer's value) |
| anything else | `CONCRETE`, `UNDECLARED_SYMBOLIC_INPUT` |

At PLAN, `causynth/RuntimeSelectedRegionFinalizer` admits every recorded occurrence that reads a
clock or a fault marker, whether or not the target demands its outputs, and seeds the demand walk
with its declared-site captures.

### 4.5 Randomness is not a root

The weave replaces `new Random()`, `Math.random()`, `Collections.shuffle(List)` and
`UUID.randomUUID()` in both passes with `runtime/Randoms`, seeded by the draw's endpoint inside the
window (by site and count before it), so a replay draws what the recording drew.

## 5. Tracked shared state (F2)

### 5.1 Which reads are tracked

A `READ_SITE` is a `field_read` or `accessor_field_return` of a cell that

- is tracked (`causynth/CausynthStaticFacts#trackedKind`), with its `trackedKind`:
  - `VALUE`: a non-static field holding an integral value, `boolean`, `byte`, `char`, `short`,
    `int`, `long`, or its wrapper (`Boolean`, `Byte`, `Character`, `Short`, `Integer`, `Long`)
    (`smt/JavaPrimitiveSmtSemantics#domainOfJavaType`). A box is immutable and a store puts a new
    one, so a wrapper field's value (or null) is all a reader observes; it is read at the
    `getfield` of the field, the box's own `value` being a projection of that read. An atomic's
    `value` is one (`AtomicInteger`, `AtomicLong`, `AtomicBoolean`'s `int`);
  - `REFERENCE`: a field a store re-points holding any other object, an array included, except a
    `String` or a float wrapper: a reader queries or projects the referent the field held when it
    read (SOLR-18406's `knownCommits`, a map each commit replaces, and `latestCommit`). A static
    one too (`static: true`: its location is its class's). A final field is none, nor a private
    one only its own class's constructors store (`#storedOnlyAtConstruction`: Lucene's
    `IndexFileDeleter.refCounts`, a lambda's captured value): its only writer is its
    constructor, so there is nothing to re-pair;
- decides a branch: the read's value reaches a branch operand within eight flows
  (`StaticScopeMap#decidingCells`, `DECIDING_FLOWS`), never through a field and never across a
  `wire_handoff` edge; a read that only feeds data stays untracked;
- is stored in `S`: some `WRITE_SITE` names the cell (`keepTrackedReads`).

`WRITE_SITE` kinds: `field_write`, `field_mutation`, `container_mutation_argument`,
`container_call_mutation_effect`, `container_array_store_value`, `container_publication`. A write
of a JDK atomic -- `AtomicInteger`, `AtomicLong`, `AtomicBoolean`, `AtomicReference`: `set`,
`lazySet`, `getAndSet`, `compareAndSet`, `weakCompareAndSet`, `updateAndGet`, `getAndUpdate`,
`accumulateAndGet`, `getAndAccumulate` and the numeric read-modify-writes -- is a write of its
`value` field (`plan/SharedFieldFlow#atomicValueField`), one table with its reads (§2.2). A
`container_publication` row is a write site of the published field whose guards shaped its
referent: carrier and cell are the field, `declaredCallee` the mutator, `publishedFrom` the local.

### 5.2 Observation

`StaticScopeMap#observedSites` lists every access of a tracked cell: its write sites and its read
sites. The concolic weave puts `ConcolicRegionRuntime.observeTrackedSite(siteId, cell, receiver)`
before each (`CausynthPipeline#instrumentConcolicObservedSites`): before the `putfield`, before the
atomic's RMW call, before the `getfield`. Inside an active region it calls the VM's
`observeField(owner, declaringClass, name, descriptor)` (`runtime/ConcolicVmBroker#observeField`),
which starts the location's log with an INITIAL version holding the current value -- an integral's
or a wrapper's word, a reference's identity -- unless a log stands (VM.md §5). A concrete store
after it is then a version, and a read states the version it saw, INITIAL when no store of the
window came first. An access before its object's constructor call, and a read site that is no
`getfield` of its cell, are left unobserved; a status the VM refuses with (`UNSUPPORTED_TARGET`
for a `float` or `double` field) is an `UNSTATED_VALUE` DIAGNOSTIC row naming it.

Each observed row states its cell's `trackedKind`; a `REFERENCE` cell's access is observed like a
value's. Not observed: a `publishedFrom` write site, whose receiver is the local's container, not
the carrier's holder (its log starts at its first model event); and a static cell, whose location
is its class's mirror: the map names it (`static: true`) and the weave passes no class owner yet.

An occurrence of a region that reads a tracked cell records its branches from region entry
(`SymbolicInputSelection#readsTrackedState`, `StaticScopeMap#trackedRegions`).

### 5.3 Guarded stores

`runtime/GuardedStoreSites#install` hands the VM one line per guarded `WRITE_SITE` store
(`methodKey`, the store as the VM names it -- `CALL <name>` from `declaredCallee`, else `FIELD
a/b/C.f` from `cell` -- then its guard site ids, tab-separated), from the map named by
`CAUSYNTH_STATIC_SCOPE_MAP`; a missing or refused table fails the session by name
(`GUARDED_STORE_SITES_*`). The VM uses it to version a concrete store at a listed site made after
one of that site's guards decided symbolically (VM.md §5.3). A `publishedFrom` write site's guards
join its store's line: SOLR-18406's `updateKnownCommitPoints` lists the `isDeleted()` branch its
`map.put` runs under (`CALL put`).

### 5.4 READ placeholders

A `DECLARED_SITE` `ACCESSOR_RETURN` whose accessor runs outside the woven program (not an
application method) and whose cell some other region stores becomes `inputKind: READ`
(`StaticScopeMap#markReads`). Keyed by site and cell (`#readSites`, `#readKey`), since the cell
alone (`AtomicInteger.value`) names every object of its type. The replay mints a placeholder there
(`runtime/RowPlaceholderMint`) that the closure binds to that location's writers.

### 5.5 Writers of a read

For a demanded read, `explore/ClosurePlanner#writers` asks the session's rows for eligible writers
and the map for the static write sites of the read's carrier (`#carriersAt`, `#writersOf`), on the
reader's node only. A recorded site's type matches a map row's by sort, or by the value it holds:
a wrapper location agrees with a row of its primitive (a stored box states its value) and with a
reference row (a stored null) (`StaticScopeMap#sameType`). A reference row states its object's
runtime class and the map row the carrier's declared type; with no class hierarchy at hand they
agree where the cell may hold the class (`#mayHold`): the same class, or value sorts that agree (a
container's shape by interface, `JavaContainerTypes#shape`; a String; a box's value). A declared
class no sort names (an application class, an interface, `Object`) holds any reference; a runtime
class no sort names may be a container, never a String or a box, both final. A `Map` field holding
a `ConcurrentHashMap` is that field's carrier. The site must also store the recorded location's
kind (`#stores`): a field store, or an atomic's write of its value, a field; any other mutator call
the state of the container its carrier holds; a read its field or, of a container field, that
container's state; and no site of the map an array element, whose write joins no carrier. COMPOSE joins a store to its carriers
by the same rule (`Composer#constructionGuards`). A read of a reference also rests on the container
each eligible store of it delivered: the closure demands the writers of every state of it the read
could have seen through that store (`Corpus#referentStates`), the states COMPOSE answers a query
through the read from.

### 5.6 Construction guards

A referent built in a writer before its publication rests on every decision that shaped it,
including one that skipped a mutation, which leaves no node in its state (R3-REFCONT §1.6).
`StaticScopeMap#constructionGuards(recordedSite, carrier)` states them for COMPOSE: the guards,
each on the arm that reaches it, of every `publishedFrom` write site of that carrier in the method
of a recorded store of it (per method, as `#sitesAt`: bci and unit index do not compare).
SOLR-18406: the store of `knownCommits` in `updateKnownCommitPoints` rests on the `isDeleted()`
branch of its loop's `map.put`.

## 6. Wire ports (F3)

A port is one carried value: every capture that writes it and every capture that reads it
(`causynth/WireFlowCatalog.WireFlow`). It states no direction or transport; the recording binds each
capture to the exchange it ran in (IDENTITY.md §7.4). Its `portId` derives from its identity and
id (`plan/CommunicationCatalogContract#portId`).

### 6.1 Declared rows

`communication-mappings.jsonl` (`-Dcausynth.communication.mappings` or
`CAUSYNTH_COMMUNICATION_MAPPINGS`, from `causynth_communication_mappings`) holds DOOR rows (§4.2)
and WIRE_FLOW rows:

```json
{"schemaVersion": 2, "kind": "WIRE_FLOW", "id": "block-key-id", "javaType": "int",
 "producer": {"method": "<...PBHelper: ...BlockKeyProto convert(...BlockKey)>", "kind": "CALL_ARGUMENT",
              "callee": "<...BlockKeyProto$Builder: ... setKeyId(int)>", "occurrence": 0, "index": 0},
 "consumer": {"method": "<...PBHelper: ...BlockKey convert(...BlockKeyProto)>", "kind": "CALL_RETURN",
              "callee": "<...BlockKeyProto: int getKeyId()>", "occurrence": 0},
 "producerFrameMethod": "...", "consumerFrameMethod": "..."}
```

Capture kinds: `METHOD_PARAMETER` (`index`), `METHOD_RETURN` (no selector), `CALL_ARGUMENT`
(`callee`, `occurrence` = the k-th call of the callee in the method, `index`), `CALL_RETURN`
(`callee`, `occurrence`). Both captures' types must equal `javaType`. A frame method is the method
one call of which builds one value instance, so same-shaped groups in one message stay apart; with
none, the message is the frame. Any other schema or kind is refused, never skipped.

SEED demands every capture and joins each producer to each consumer (`wire_handoff`,
`wire_capture_argument` edges), so the slice continues on the sending side.

### 6.2 Protobuf derivation

`SeedBackwardStaticAnalyzer#deriveWirePort`: a demanded `x = r.getF()` with no parameter, returning
a primitive or `String`, on a message an RPC carries, is the consumer of port
`auto:<SimpleName>.<F>`. Its producers are argument 0 of every call of `<M>$Builder.setF(T)` in the
analysed program (the application classes in scope). A capture a declared row already holds stays
that row's; a port with no producer derives nothing. A derived port names no frame method.

A message an RPC carries (`#rpcMessages`) is a protobuf message (its hierarchy reaches
`*.protobuf.GeneratedMessage` or `*.protobuf.GeneratedMessageV3`) that is the request or the
response of a protobuf service method, or that a field of such a message holds, transitively (an
instance method returning a protobuf message: a singular or repeated field getter). A service method
is one whose first parameter is `*.protobuf.RpcController`: the shape protoc emits for an `rpc`,
which the system's RPC engine proxies on the client and dispatches on the server, so every call
crosses the transport's door (Hadoop: the IPC door in `Client`). The services are those of the
loaded program (Soot resolves the analysis scope's references transitively), read once, at the
first demanded getter. The rule does not read the DOOR rows: which transport serves a proxy is
decided at run time, where no static pass follows it. A message no service reaches (an fsimage
section, an edit-log record, a DataTransfer op) is written to a file or a stream that no door
carries values over, and derives no port.

The rule is by type. A message that an RPC carries and a stream also writes (`ExtendedBlockProto`,
in `LocatedBlockProto` and in a DataTransfer op header) exports at every setter call, including one
whose message never reaches a door.

### 6.3 At run time

The OUT capture exports the carrier leaf's expression through the VM (`runtime/WireExport`) and
stages the handle on the thread's outbound envelope (`runtime/SymbolicMessageEnvelope`, schema
`CSE5`, at most 64 entries and 64 frames per message), which the next outbound door of that thread
carries (IDENTITY.md §7). The IN capture takes the element by (frame, port, ordinal), attaches it,
and `runtime/HandoffMint` mints a fresh `v_H` per primitive leaf, named by (port, consumer
occurrence, k-th attach, element path), at most 64 leaves per attach. The export row and the attach
row are paired by the VM handle, else by correlation and port (`runtime/Interactions#pairing`). A
refused export or attach files a gap on the occurrence it ran in, with the port and the VM status
(`WireExport#refused`): an attach no admitted activation runs is a DIAGNOSTIC `ADMISSION_GAP`
beside that activation, stated unselected; one inside an admitted activation is DIAGNOSTIC
`UNSTATED_VALUE`, since its rows compute on the arrived value as a constant; a refused export is
DIAGNOSTIC `UNSTATED_VALUE`. An accepted attach that mints no `v_H` is DIAGNOSTIC `UNSTATED_VALUE`.
A refusal is its frame's: COMPOSE refuses the paths and arms whose closure reaches an occurrence its
session filed an `UNSTATED_VALUE` row on, and nothing else (`compose/Composer#frameRefusals`).

## 7. Current limits

- Roots are clocks recognized by the call-return rule, declared door faults and tree hooks. A clock
  read through a field, a parameter, `java.time`, or an interface whose implementation is outside
  the scope is not recognized; configuration values and pre-window state are roots only where a
  tree hook says so.
- The VM versions integral instance fields, wrapper fields, `REFERENCE` cells (reference fields
  and `AtomicReference.value`) and the atomics' integral `value` from an observed access (§5.2); a
  static cell is not observed (the weave passes no class owner). A container reached through a
  replaced reference is the referent's state its store stated (`referentState`), which COMPOSE
  asks per candidate (PIPELINE §8). Not tracked: `float`/`double` fields, static values, `String`
  fields, array elements, and containers the VM does not model (`TreeMap`, `TreeSet` and the
  queues are classified by interface here, modeled by R3-REFCONT WP3b/c).
- A non-application call's receiver is dropped from the slice (§2.2) unless the call is a
  container query or an atomic's accessor, so state behind any other library object never
  enters `S`.
- Control dependence ignores exception edges and follows a call up only for constant stores,
  field-effect calls and write-site guards (three calls up); it never crosses a thread start, an
  executor submission or the wire.
- Derived ports cover only scalar getters of protobuf messages a protobuf service carries, with a
  setter call in scope: no repeated, enum, `bytes`, nested or map-keyed fields, no string codecs,
  no frames, no message of a transport without services (DataTransfer ops, HTTP bodies, ZooKeeper
  nodes). `String`, boxed and reference leaves get no `v_H`. Every other cross-process value needs
  a declared row.
- Growth is capped by `causynth_scope_growth_budget`, spent nearest-first on every class a row
  resolves to (all CHA implementations), and never reaches classes outside the lineage roots.
