# Symbol scope: what is symbolic, and from where

SEED computes one static slice `S` backwards from the declared throw and publishes, per site of
`S`, what a replay does there: mint a root, observe shared state, export or attach a wire value, or
nothing. Java paths below are under `src/main/java/edu/uva/liftlab/graphchecker/`.

Three things are kept apart:

- a **root** is a fresh symbol the replay mints (a clock reading, a fault marker, a configuration
  value or a tree's configured source). Only roots add freedom; each states its category (`CLOCK`,
  `FAULT`, `CONFIG`, `READ`, `HOOK`, `contract/RootCategory`): what moving it means.
- a value is **symbolic by propagation** when the VM's shadow carries an upstream root's expression.
  The VM propagates through every bytecode a region's thread interprets, whatever the analysis
  scope (VM.md); the slice decides only where roots, tracked reads and ports are.
- a **tracked** location is one the VM versions from its first observed access, so COMPOSE can
  re-pair a read of it with another writer (a STATE family).

## 1. The rule

| where a value comes from | what it is | bound by |
|---|---|---|
| **F1** the environment: a clock read, a door fault, a configuration value, a tree's configured source hook (§4) | ROOT | its domain: a marker (a boolean configuration too) both values, an integral configuration the hull of its anchors (§4.3), a hook's source its `root-domains.jsonl` row (none: pinned), a clock its window (`contract/RootKind`, `contract/RootDomain`) |
| **F2** a read of shared state another occurrence writes (§5) | TRACKED READ, or a READ placeholder where the accessor is unwoven | the version it observed, and every attested writer occurrence of the same session or the location's INITIAL the read could have run right after (`smt/Arms#stateArms`, the one rule `#eligible`) |
| **F3** a message leaf that crosses a process (§6) | WIRE ATTACH, a fresh `v_H` per primitive leaf | the producer's export, paired within the run (message families) |
| **F4** a return or parameter from code outside the analysis scope | grow the scope (§2.4); what stays outside has no root, tracked read or port, and is symbolic only by propagation | its inputs' expressions, else the recorded value |
| a read of state from before the window | the INITIAL version of its log, a write row (`contract/WriteRow#initial`): the writer at version 0 | joined to what it held, an arm of F2's |

A value no rule makes symbolic is concrete: `plan/ConcolicScheduler.SymbolicInputSelection` marks
every other proposed input `CONCRETE` (`UNDECLARED_SYMBOLIC_INPUT`), and its expression, if any,
still rides with the value. A root with no domain is pinned (`RootDomain`). A read COMPOSE cannot
bind is pinned to its recorded value or refused as `UNSTATED_VALUE` (`compose/Composer`).

## 2. The slice `S`, and its scope

`causynth/SeedBackwardStaticAnalyzer#analyze`, run by `causynth/CausynthPipeline#analyze` after
`DoorWeave.apply()` (§4.2), so every pass sees the woven doors as program text.

### 2.1 Seeds

- The declared throw (the target spec's class and line, `ExceptionTargetLineResolver`; one Jimple
  throw or the analysis refuses): the
  thrown value (`exception_throw`) and the operands of every branch from which the throw is
  reachable (`exception_guard`).
- Every capture of every declared WIRE_FLOW port (`seedDeclaredWireFlows`), whether or not the throw
  needs it.
- Every call of `Debug.makeSymbolicBoolean` (`seedExplicitFaultEntries`): its result cell and the
  guards of that call.

### 2.2 Propagation rules

The worklist (`runWorklist`, `processMethod`) walks definitions backwards:

- **Locals, arguments, returns** into callees whose body is analysed: a concrete method of an
  application class, an abstract class's or an interface's default one included, that is not a
  structural field accessor (`isExpandableMethod`). A call whose CHA targets include the callee
  itself (a concrete method an abstract class declares and its subclasses inherit: HDFS's
  `BlockInfo.isComplete()`, `getBlockUCState()`) is the plain call for that target -- its
  `call_argument` and `call_return` rows and its body -- and dispatched to the others.
  Callers of a demanded formal or of a demanded `this`, constructor callers, and CHA dispatch to the
  application implementations of an interface or abstract call (`processDispatchInvoke`; owners in
  `java.`, `javax.`, `com.google.`, `org.slf4j.` are not dispatched). A call is indexed under the
  type it is made through and under the analysed method that type declares or inherits (`Sub.m()`
  is a call of `Base.m()`), and an implementation's callers are found through every interface or
  abstract supertype that declares or inherits the method, Object's methods aside
  (`resolveDispatchSources`: `Spi.m()` of an `interface Spi extends Probe`, whatever package declares
  `Probe.m`). A helper that mutates the container it is passed or is (`this` of a JDK container's
  subclass) mutates the caller's (`container_call_mutation_effect`).
- **Matched calls** (`causynth/ReturnOnlyFormals`): a demanded formal or `this` that only its
  method's return needs is demanded at a call only where that call's result is demanded
  (`propagateCallArguments`, `expandCallerArguments`, `expandCallerReceiver`); one that an effect of
  the method needs -- a field store, a store into a container or array reached from a formal, `this`
  or a field (through copies, reads, views and call results, not through what was stored into it), a
  container publication or argument mutation, the declared throw, a `.throws`, a wire capture, a
  guard of another method's store or activation, a call passing it to such a formal or to a
  constructor -- is demanded at every call, as is one flowing into both. The
  summary is read off the slice's rows that touch the method's cells: backward from its return, and
  backward from each effect origin, through a call inside it to a return-only formal as through the
  call's result. A virtual call is decided per CHA target (each implementation's summary, the union at
  the site); a call of the method itself is a flow inside it; a cycle through other methods is
  conservative (no formal of a method whose summary is being computed is return-only); a library call
  keeps its contract. A formal once an effect stays one, and its turning re-queues its method, whose
  next pass demands it at every caller the call index finds, and every caller that met it while it
  was return-only (`ReturnOnlyFormals#demanded`, the one rule the three walks ask), whose next pass
  demands it there. Without it the slice entered a helper through its return at
  one call and left through every caller's argument: hdfs-11741 on the W6 tree entered
  `PBHelperClient.getByteString(byte[])` at `convert(BlockKey)` and left through its 17 other callers,
  SASL's `convert(CipherOption)` among them, to `DNConf.encryptionAlgorithm`, and rooted a new region
  at `SaslDataTransferServer.getEncryptedStreams` over the declared target's.
- **Field jump**: a demanded read of an application field demands every write of that field in the
  scope (`expandFieldWriters`). Field-level, not per object.
- **Control dependence**: a demanded definition demands the operands of every branch from which it
  is reachable by a proper subset of the branch's successors (`demandControllingGuards`,
  `SiteControlDependence.MethodGuards#reaching`), published as `guard_dependency` edges.
- **Door faults** (`causynth/FaultPropagation`): a *raise* is a unit that can throw a door kind (a
  catalog door's checked exception, §4.2): a woven door throw (`DoorWeave#woven`), a call whose
  targets (CHA over the analysed program) let one escape, a call of an application interface method
  no analysed class implements that declares a supertype of the kind (a proxy: it raises the kinds
  of the doors an analysed `InvocationHandler#invoke` reaches by calls), and a handler's rethrow of
  what it caught (a `finally` or `synchronized` block). A kind goes to the handler of the first trap
  covering the raise that catches it, else it escapes the method; to a fixed point. A call that can
  leave a fault to a handler is a *fault branch* (§3): the sites only one of its exits reaches
  depend on it, and its operand is `<callee>.throws` of each callee it escapes. So is the marker
  branch of a woven throw a handler of its own method catches (a door at calls): its throwing arm
  reaches the handler only over the fault edges, and without it the handler, reached from both
  exits of every earlier fault branch, would depend on nothing. A demanded
  `<m>.throws` (`expandThrows`) takes an `exception_flow` edge from the origin of each raise a fault
  escapes `m` from -- the woven throw's marker local, a callee's `<callee>.throws` -- under the
  raise's guards, so a handler's effects lead back to the door's marker.
- **Activation**: a branch that decides whether code carrying the slice's data runs is demanded
  like data (owner 2026-10-04). Within a method that is the rule above, and a mutation of a
  demanded container -- a local's (`list.add` under `if (...)`), a helper's mutation of one it is
  passed, an array store -- demands its own guards, guarding the container's cell. Across calls
  (`expandActivationGuards`, `ACTIVATION_DEPTH` = 3, `SiteControlDependence`'s `CALL_DEPTH`): for
  the declared target's method and for every method holding a demanded store or container
  mutation, constant or not, each call into it, three calls up, dispatch included, demands its
  deciding operands -- its branches and door-fault branches -- in its method, guarding the
  method's `<m>.activation` or the stored cells; a dispatched call links the caller to the method
  it runs (`dispatch_activation`). hdfs-adhoc-29's anchor leaves `BlockRecoveryWorker
  $RecoveryTaskContiguous.recover()` at `candidateReplicaCnt > 0 && syncList.isEmpty()`, the
  guard of its call into `syncBlock` and on to the target's `getActiveNamenodeForBP`: the count
  rests on `initReplicaRecovery`'s answer, which `FsDatasetImpl.initReplicaRecoveryImpl` gives
  only past `rur.getRecoveryID() >= recoveryId`, so `ReplicaUnderRecovery.recoveryId` is read on
  the anchor's way. SOLR-18406: Lucene's `CommitPoint.delete()` sets `deleted = true`, and Solr's
  deletion policy calls it through `IndexCommit.delete()` only when the commit's reservation, a
  clock, has run out. A call's demanded result needs no rule of its own: the call's definition
  is demanded, and with it the call's guards.
- **Field reads**: a demanded `x = b.f` demands `f` (`field_read`, then the field jump) and `b`,
  the object it reads from (`local_def_use`: the base is a use of the read), as an accessor's
  receiver (`accessor_receiver`) and a dispatched call's (`dispatch_receiver`) are. A reference
  read only to reach a projection (SOLR-18406's `latestCommit`, whose generation the throw
  compares) is therefore a cell a branch decides through (§5.1).
- **Library calls**: the result of a non-application call depends on its arguments, and on its
  receiver by one of these rules: `String`, `StringBuilder`, `StringBuffer` and every wrapper's
  unboxing accessor (`smt/JavaPrimitiveBoxing#unboxing`, `Boolean.booleanValue` included) keep
  the receiver as a value (`isValueLikeLibraryInvoke`), as do the final methods every enum
  inherits from `java.lang.Enum` (`equals`, `hashCode`, `compareTo`, `ordinal`, `name`), called
  on an application enum with no body of its own (`getBlockUCState().equals(COMPLETE)`), their
  arguments values too; a JDK atomic's `get()` is an accessor of
  its `value` (`AtomicBoolean.get()` is `value != 0`), read off a table rather than its body
  (`plan/SharedFieldFlow#atomicRead`, `StructuralFieldAccessorProof#atomicField`); a container
  query depends on receiver and arguments (`processSemanticContainerOperation`,
  `container_receiver`, `container_argument`); and any other library call on a receiver that is
  shared state -- its definition, through copies and casts, is `this`, a field read or a
  structural accessor's result -- depends on it (`processLibraryReceiver`,
  `causynth/LibraryReceivers`, `library_receiver`, `dependencyRole VALUE_FRONTIER`):
  `lock.isWriteLockedByCurrentThread()` on a field's lock, a ZooKeeper client's `zk.getState()`.
  A library is code no class root of the system holds (`LibraryReceivers#systemClasses`, over
  the campaign's `causynth_lineage_roots`, `-Dcausynth.lineage.roots`; a static pass that meets a
  library call with no roots stated is refused by name): a call into the system's
  own code outside the scope is the frontier's (§2.4), where the slice stops and scope growth
  takes the class whose body says what the result rests on. Not a receiver the method allocated
  or was passed, not a call on `Object`, `Class`, a logger or a `metrics` package, and not a
  clock, whose value is a root (§4.1).
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
  `Collection` and `Iterable` are contracts too (`stream()`, `parallelStream()`, `forEach`,
  `toArray`, ...: a map view's stream is `Collection.stream()`), and a *stream* is a query over
  its source: every call of a `java.util.stream` pipeline (`BaseStream`, `Stream`, `IntStream`,
  `LongStream`, `DoubleStream`) and of `Collectors` reads its receiver, if any, and its arguments.
- **Functional arguments** (`enterFunctionalArguments`): a functional object a demanded container or
  stream call takes (a filter's predicate, a `map`'s function, a `removeIf`, `computeIfAbsent`,
  `merge` or `compute` callback) contributes its functional method's return: a `functional_return`
  edge from that method's return to the argument, and the slice enters the method -- each method of
  the object's class implementing an abstract method of a `java.util.function` interface or of
  `Comparator` it implements. The class is the one the argument is created from: a `new C`, or the
  static factory of a functional class (Soot's desugared lambda or method reference, `X$lambda_m_N__k`,
  and its `bootstrap$`). What the object captured reaches the factory's arguments at the creation
  site through the constructor-object edges (`cap0` written by its constructor, read in its method).
  hdfs-bugs `slowdisk-zero` (bug #15): `FsVolumeList.chooseVolume`'s `list.stream().filter(v ->
  !slowDisksToExclude.contains(...)).collect(toList())` reaches `DataNodeDiskMetrics
  .slowDisksToExclude`, its detector store under `maxSlowDisksToExclude > 0`, and
  `setMaxSlowDisksToExclude`, the reconfiguration's writer.
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
| `communication_gaps.jsonl.gz` | ports or loops the planner could not place, and the configuration reads left concrete (§4.3) |
| `static_scope_map.jsonl` | §3; built before any hook is woven, over the door-woven bodies (§4.2), so site ids are the unit indices every pass and every replay decides at; and a `CONFIG_KEY` row per configuration root (§4.3) |
| `scope_frontier.jsonl` | §2.4 |
| `root_demand.jsonl` | §4.6: every boundary where the values the throw's path guards decide on enter, every path cut at the bound, and why each is not chosen |

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
   cell back to the throw's sinks); a row the root demand chose as a boundary (§4.6: a `SCOPE`
   callee or formal, a `PRE_WINDOW` field) states its class as `demand`, and demanded rows come
   first, the rest after, each nearest first:
   - `CALLEE`: a callee whose return `S` demands but whose body is not analysed (and is no clock
     and no configuration getter: a root, §4.1, §4.3);
   - `FIELD`: a field `S` reads or stores;
   - `FORMAL`: a method whose primitive or `String` formal `S` demands only through a field. A
     formal reached without a field in between is on the target's own call chain and is never a
     row: growing its callers would move the region root and with it the target's identity;
   - an IO frontier `CALLEE` (`demand` IO, §4.6): a call into the system where a local file
     fault could stand, though `S` demands no return of it.
2. `plan/ScopeGrowth` resolves each row over the classes of `causynth_lineage_roots`:
   - `CALLEE`: the class whose body runs it (for an abstract method, the class each implementation
     inherits it from), unless that body only loads constants;
   - `FIELD`: its owner and, unless the field is private or final, every class storing it; a
     static final field is a constant and grows nothing;
   - `FORMAL`: every class calling the method;
   - an IO row: the class whose body runs the called method, only when that body itself calls a
     demanded door's anchor (listed as `IO` in `GROWN`), else it is skipped and named in the
     step's summary (one level per growth round);
   - never a generated protobuf class (a supertype in `*.protobuf.*`).
   Each class taken is copied into `<causynth_output_dir>/scope-classes/` and listed in `GROWN`
   (`class`, `kind`, `signature`, `distance`) until `causynth_scope_growth_budget` classes
   (default 24; `0` disables growth) are grown, taking the rows in the frontier's order.
3. The grown directory joins every later pass as `-Dcausynth.process.dirs`: one application scope.

Only classes under the lineage roots are indexed, so nothing else (the JDK, a library jar) is
ever grown by a row. Before the first pass, outside the budget, the door step copies the class
families of the library doors the system calls (§4.2), from a library jar too.

## 3. The static scope map

`plan/StaticScopeMap` builds `static_scope_map.jsonl` (`#sites`, `#rows`) from the edges and the
region skeletons. One row per (role, region, site); every row states `schemaVersion` 1,
`kind: STATIC_SCOPE_SITE`, `role`, `regionId`, `siteId` (`<method>#u<unitIndex>`), `vmSite` (the
method as the VM spells it, the join with recorded endpoints), `cell`, `carrier`, `portId`,
`guards` and `guardOutcomes`.

| role | one row per | extra members |
|---|---|---|
| `TARGET_SITE` | the declared throw | `chain`: the guards of its guards within the method, each on its arm toward the throw (`Guards#chainOf`), then the guards of the calls into its method, three calls up, never into an execution context's entry (a thread's or task's `run`, a `call`, a `main`: its starter runs it) (`StaticScopeMap#targetChain`, `Guards#callsInto`): the decisions its occurrence takes on the way to the throw. The static planner roots a region at the target's method itself (`FAILURE_TARGET_ENTRY`), but its callers' region is the occurrence it folds into at run time |
| `ROOT_SITE` | a call site whose `<callee>.return` defines a local of its method | `local` |
| `DECLARED_SITE` | a value entering from outside the slice's text: an `ACCESSOR_RETURN` (a structural accessor; cell = the field) or a `CALL_RETURN` (a clock, a configuration getter, a fault marker) | `declaredKind`, `edgeId`, `dependencyCell`, `javaType` (primitive only), `implementationMethod`, `inputKind` (`CLOCK`, `FAULT`, `READ`, `CONFIG`, or absent), `clockNanos` and `clockSource` (a clock's tick and the JVM clock it wraps, `currentTimeMillis` or `nanoTime`, read off the wrapper's body by `causynth.RootCatalog`; absent for a wrapper mixing both), `sourceId`, `domainMin` and `domainMax` (a configuration's root and static domain, §4.3), `marker` (a fault marker's name, §4.2), `demandDistance` (the root demand's distance to this read, §4.6) |
| `READ_SITE` | a read of a tracked cell (§5.1) | `trackedKind` (`VALUE`, `REFERENCE`, `CONTAINER`), `static` (a static field), `demandDistance` (§4.6) |
| `WRITE_SITE` | a store or container mutation into a field `S` names | `declaredCallee`, `callers`, `publishedFrom` (the local a publication mutates, §2.2), `static` (a store into a static field), `constructionOnly` (a store into the field itself that only its class's construction stores, §5.1) |
| `EXPORT_SITE` | the producer capture of a port (OUT side only) | `portId` |

**Guards** (`causynth/SiteControlDependence`): site `t` is control-dependent on branch `b` when
some successor of `b` is post-dominated by `t` and `b` is not; the outcome names the arm that
reaches `t`. The CFG has no exception edges (`BriefUnitGraph`), but for door faults a handler
catches (§2.2): over the CFG with those edges, a site also depends on each fault branch (a call
that can leave a fault to a handler) that decides it, with outcome `null` (no decision is ever
recorded at a call; a fault flips at its marker), and on that call's own guards; a woven marker
branch that is a fault branch carries its arm toward the handler. A fault branch
adds to a site's guards and never takes a branch's place, so a recorded branch is never hidden
behind a call. A `WRITE_SITE` also carries the
guards of the calls into its method, up to three calls up (`Guards#callsInto`, `CALL_DEPTH`), and
those callers (`Guards#callersOf`). A guard `v ==/!= c` (`c` an int or null) on the result of one
call of an application helper names the helper branch arms that decide it (`causynth/BooleanReturns`,
`guardDeciders`): every arm of a helper branch that runs straight (constant stores, jumps, at most
16 units) to a return of a constant of `c`'s kind -- a branch whose two arms return constants the
guard takes alike decides nothing, a helper with a switch has none -- each with the deciders of
the nested helper return its branch tests, three helpers deep (hdfs-adhoc-40's
`!isSufficientlyReplicated(b)`: the helper's first branch tests `hasMinStorage`'s return and
returns true on one arm, its second compares the live count). At run time the decision that chose
the return is the latest one in the helper's method before the guard, when it is a decider arm, and
a concrete one is decided by its nested helper's in turn (`runtime.RowPublication#decidedBy`).

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

Doors are the engine's, not a case's: the `DOOR` rows of the library catalog
(`src/main/resources/edu/uva/liftlab/graphchecker/library-catalog.jsonl`, read by
`causynth/LibraryCatalog`), woven by `causynth/DoorWeave`:

```json
{"schemaVersion": 1, "kind": "DOOR", "transport": "HADOOP_IPC", "direction": "REQUEST",
 "method": "<...Client$Connection: void sendRpcRequest(...Client$Call)>",
 "after": "<...RpcWritable: void writeTo(...ResponseBuffer)>",
 "faults": ["java.io.IOException", "org.apache.hadoop.net.ConnectTimeoutException"]}
```

| transport | direction | door method | anchor |
| --- | --- | --- | --- |
| `HADOOP_IPC` | `REQUEST` | `Client$Connection#sendRpcRequest` | after the request's `RpcWritable#writeTo` (serialized, not yet queued) |
| `HADOOP_IPC` | `RESPONSE` | `Client#getRpcResponse` | after `CompletableFuture#get` (trunk); before `Call#getRpcResponse` (3.4) |
| `HDFS_SASL` | `REQUEST` | `SaslDataTransferClient#doSaslHandshake` | before `DataOutputStream#writeInt` |
| `HDFS_DATA_TRANSFER` | `REQUEST` | `datatransfer.Sender#send` (every op) | before `DataOutputStream#flush` |
| `HDFS_DATA_TRANSFER` | `RESPONSE` | every analysed caller (no door method) | after `BlockOpResponseProto#parseFrom(InputStream)` (an op's response), `DNTransferAckProto#parseFrom(InputStream)` (a transfer's close ack), `PipelineAck#readFields(InputStream)` (a write pipeline's ack) |
| `SOLR_HTTP` | `REQUEST` / `RESPONSE` | `HttpSolrClient#executeMethod` | before / after `HttpClient#execute` |
| `SOLR_HTTP2` | `REQUEST` / `RESPONSE` | `Http2SolrClient#request` | after `InputStreamResponseListener#<init>` / after its `get(long,TimeUnit)` |
| `ZOOKEEPER` | `WRITE` | `ZooKeeper#{create (two), setData, delete, multiInternal}` | after `ClientCnxn#submitRequest` (the write happened; the client sees the failure) |
| `LOCAL_IO` | `OPEN`, `READ`, `WRITE`, `SYNC`, `NAMESPACE` | a demanded call only (below) | before the call: the failed operation never happens |

**Demanded doors.** A local file operation is a door only where the root demand chose its call
(§4.6): its result or its failure flows into what the slice traces, never every IO call of a class
or method (owner, 2026-10-04). Its rows state `"sites": "DEMANDED"`, no `method`, `before` the JDK
call, and either the kind the call declares -- `FileNotFoundException` for the `FileInputStream`,
`FileOutputStream` and `RandomAccessFile` opens, `SyncFailedException` for `FileDescriptor#sync`,
`IOException` for the other stream and `RandomAccessFile` reads, writes, `seek`, `setLength` and
`close`, the `FileChannel` opens, reads, writes, `force`, `truncate`, `transfer*` and
`position(long)`, the `Files` opens, reads, writes, copies, moves, deletes and creates, and
`File#createNewFile`/`createTempFile` -- or the `result` the call returns instead of failing:
`false` for `File#renameTo`, `delete`, `mkdir(s)`, `setLastModified`, `setReadable`/`Writable`/
`Executable`/`ReadOnly`, `null` for `File#list`/`listFiles`. A call is a door's only as the
catalog spells it: a write through a variable typed `OutputStream` may be a socket's, and a
socket's failure is a transport door's. An observation (`exists`, `is*`, `can*`, `length`,
`lastModified`, `*Space`, `FileChannel#size`) is never a door: its value is the disk's state, not
an operation's outcome. The chosen calls are `io_doors.jsonl` beside the scope map (`causynth/
DemandedDoors`: caller, callee and the call's ordinal among the caller's calls of that callee in
body order, never a unit index, which a door shifts); every pass weaves them before any analysis
(`-Dcausynth.io.doors`, `run_engine.sh` `do_analyze`), a throwing door as the catalog's doors are,
a failing result as `r = marker ? failing : call(..)`, so the call does not run on the fault arm.
A failing result's checked throw -- the first test of the result the call falls through to, and
each throw its failing arm reaches that its other arm does not (`if (!f.renameTo(g)) throw new
IOException(..)`) -- is a raise of the door's marker (`causynth/FaultPropagation`), so the fault
flows on as a thrown door kind does. A site the file names that no catalog row or no analysed call
answers, or a call that already holds a door, is refused (`DEMANDED_DOOR_UNAVAILABLE`). A demanded
door's marker roots no region (§4.6).

A door keeps the pairing its call made: a request door lies after the tree's outbound message hook
(or before anything is sent: the SASL magic number), a response door after its inbound hook, a
store door after the store hook. Where a system's own hook follows the library's call, the
library anchor cannot be there, and the system states only where its hook sits: a `HOOK` row of
`experiments/<system>/doors.jsonl` (`run.sh` passes it as `-Dcausynth.system.doors`) names a catalog
door (`transport`, `direction`, `door`: its method) and the system call after which it is woven
(`method`, `after`); the door keeps the catalog's kinds, no door is added or dropped, and a `HOOK`
naming no catalog door, or a `DOOR` row in a system's file, is refused (`LibraryCatalog#placed`).
Solr's: `ZooKeeper#setData`, `#create` and `#multiInternal` in `SolrZkClient#setData`, `#create`
and `#multi` after `causynthWrote` (the store hook `MessageDoors.stored`; in `multi`, after the first
operation's, so a multi's later operations are unpaired under a fault); the `SOLR_HTTP` and
`SOLR_HTTP2` responses after `CausynthHttp#response` (in `HttpSolrClient#executeMethod` and
`Http2SolrClient#processErrorsAndResponse`). HDFS's: the trunk line's `HADOOP_IPC` response in
`Client#getRpcResponse` after `installCausynthResponse`, the response's inbound hook (the 3.4 line's
catalog anchor already follows it). These rows are the tree adapters' hooks spelled out; they go
when the engine finds a door's following hook itself (a hook call of the door method or of its
caller after the anchor). There is no door on a data read (DataTransfer's `PacketReceiver`, ZooKeeper
`getData`/`exists`/`getChildren`): every packet and cluster-state read would be one.

A row with no `method` is a door at calls: a library call whose outcome each caller reads where it
makes it. A caller that an execution context or the target already roots keeps that region (its
address and, holding the failure, its exception context; `causynth/SymbolicRegionPlanner`): rooted
anew as an explicit fault entry and selected as a fault context, `BlockReceiver$PacketResponder#run`
lost BlockReceiver-1448's throw (`FATAL_TARGET_NOT_IN_WINDOW`). A caller no other rule roots (a
communication endpoint such as `DataXceiver#writeBlock`) is an explicit fault entry, so its address
is not the one it had before its door. DataTransfer has no response method of its own: every side that sent an op (the client's
`DataStreamer`, a DataNode's mirror in `DataXceiver#writeBlock` and its `DataNode$DataTransfer`, the
`Dispatcher`, a `BlockReader`) parses the response itself, so the door sits after the first call of
the anchor in every analysed method that makes one, and its fault goes to that caller's own handler
(`BlockReceiver$PacketResponder` tells an `EOFException` from other failures). A door at calls has
no family: it is woven where the analysis scope already holds the caller, and a scope with no caller
has none.

A door with a method applies where its class family (the method's outermost class with its nested
classes) is analysed. `plan/ScopeGrowth --doors`, before the first static pass and again after every
growth, outside the growth budget (§2.4, `run_engine.sh campaign_scope_doors`), copies into
`scope-classes/` the family of every door that a class of the analysis scope (the case's scope and
what it grew) outside the family calls, from the first of the roots and the workload classpath
holding it (the system's own classes or a library jar), unless the scope holds it; its `GROWN`
lines have kind `DOOR`. A class of the roots the scope never reached brings no door (hadoop-common's
`ActiveStandbyElector` calls ZooKeeper, which no HDFS case's slice reaches).

At the first call of `after` (or before the first call of `before`) in `method`, the weave inserts,
per fault kind in row order, `if (Debug.makeSymbolicBoolean(name)) throw new Kind("symbolic
<name>")`, the false arm falling to the next marker. `name` is `FAULT:<TRANSPORT>:<DIRECTION>` for
`java.io.IOException` and `FAULT:<TRANSPORT>:<DIRECTION>:<SimpleName>` otherwise. Rows of one door
method (transport, direction, class and method name) are its signatures on different library lines;
where the family is analysed, every row that resolves is woven and a door method none of whose rows
resolves is refused (`DOOR_METHOD_UNAVAILABLE`), as is an exception class that does not resolve
(`DOOR_FAULT_KIND_UNAVAILABLE`). A kind is an environment failure the transport can raise and a
caller tells apart (a retry policy fails over on one and retries another); a semantic server
exception is never a kind, it must come from the causal chain. The weave runs before any analysis
(`CausynthPipeline#run`), so every pass numbers units over the same woven body and site ids agree
across passes; they differ from the unwoven method's. The woven units are tagged
(`DoorWeave#isWoven`): a declared throw's ordinal among its method's constructions of its type is
the class file's (`ExceptionTargetLineResolver`), so the seed counts only the program's own (a door
at calls in the method that holds the throw, `Dispatcher$PendingMove#receiveResponse`).

The catalog's rows each state `schemaVersion 1` and their `kind` and are keyed by
`library-catalog.jsonl:<line>`, the shape `contract/WireDeclarations` reads (CONTRACT-SPEC §6.1). A
malformed row, a member its kind lacks and a row stated twice are refused by name. `CONFIG_SOURCE`
rows (`method`, `keyArg` naming the String key argument, optional `defaultArg`) list configuration
getters (Hadoop `Configuration.get*`, Solr `getClusterProperty` and `XmlConfigFile.get*`);
`CONFIG_FIELD_OWNER` rows (`class`) name a configuration object built from a file no getter of the
catalog reads, whose every field is configuration (Solr's `NodeConfig`, `CloudConfig`). Both are
`causynth/ConfigRoots`' (§4.3).

A `FAULT:` marker is a `DECLARED_SITE` (`inputKind: FAULT`) iff its transport is a catalog door's
(`StaticScopeMap#declaredFault`, `LibraryCatalog#transports`); a marker whose name does not start
with `FAULT:` is the workload's own and always declared. The recorded polarity is `false`. The
row states the marker's name (`marker`), and so does the input it plans (`DECLARED_FAULT_MARKER`): a
replay that answers a message door's marker `true` ends the thread's request in hand by it, as a
native plant does (IDENTITY.md §3, `Identity#doorFaulted`). How fault decisions become flip sites
is IDENTITY.md §7.

### 4.3 Configuration and configured sources

Configuration is recognized by category, as a clock is (`causynth/ConfigRoots`, over the slice):

- a *getter*: a JVM one (`System.getProperty`, `System.getenv`, `Boolean.getBoolean`,
  `Integer.getInteger`, `Long.getLong`) or a `CONFIG_SOURCE` row of the library catalog (§4.2),
  called on its class or a subclass (Hadoop's `HdfsConfiguration`);
- a *wrapper*: a method every return of which is a configuration value of one key in one shape --
  its key a literal, or the wrapper's own `String` parameter -- followed four wrappers deep (Solr's
  `Overseer.isLegacy`, `"true".equals(getClusterProperty(LEGACY_CLOUD, "false"))`). A getter
  call in a wrapper's body is the wrapper's read: its callers mint it;
- a *field*: an integral or boolean instance field every writer of which, over the whole analysed
  scope (`StaticProgram#fieldWriters`), stores a configuration value of one key in one shape, or a
  constant that a store of the configuration post-dominates in the same method (an initializer it
  overwrites, javac's `boolean legacy = false;` before the constructor's store) -- hdfs-17960's
  `SnapshotManager.snapshotDeletionOrdered`, stored once, in the constructor, from
  `conf.getBoolean("dfs.namenode.snapshot.deletion.ordered", false)` -- or such a field of a
  `CONFIG_FIELD_OWNER` class, its own key. A getter call its writers store is the field's read.

A configuration value is a getter's or wrapper's return through locals, casts, a parse or an
unboxing (`Integer.parseInt`, `Boolean.parseBoolean`/`valueOf`, `intValue`, `trim`), a literal's
`equals` (a *view*) and `Math.max`/`min` with a constant (a *clamp*); arithmetic makes another
value. Its key is the key argument where that is a literal (javac inlines a `static final
String`); a read whose key no literal names is no root. Its root is `CONFIG:<key>`, or
`CONFIG:<key>==<literal>` for a view: `"a".equals(get(k))` is not `k`, nor the `"b"` view. Its
*shape* is its view, its clamps and its type. A key is minted only where
the root demand chose it (§4.6): its nearest read within sixteen edges of the throw's path guards
on the cone, among the twelve nearest keys. One key is one root, minted in one shape: at each read
of the key's field (the first by signature where a field holds it), else at the return of each
getter call of the shape of its first call (by site), a `DECLARED_SITE` `CALL_RETURN` with
`inputKind: CONFIG`, its `sourceId` and domain (the plan's input action states them as
`configSource`, `domainMin`, `domainMax`). Only an integral or boolean value is minted.

- **The field's reads.** `causynth/StaticSymbolicSourceDiscovery` declares each read (`getfield`)
  of a configuration field in a region's text -- its methods and their application callees -- as it
  declares a hook site (below), under the authority `EXACT_STATIC_CONFIG_READ_SITE_V1`; the
  recording's read of the field there (a `FIELD_READ` trace event) is the site's evidence in an
  occurrence (`runtime/RuntimeRegionPlanner#configuredSourcePhases`). Before the `getfield`,
  INSTRUMENT weaves `ConcolicRegionRuntime.readConfiguration(sourceId, owner, field)` under the
  site's context (`CausynthPipeline#instrumentConfigurationRead`), the hook a tree would have
  carried; it never throws into the read, and a failure is named (`UNSTATED_VALUE`, BLOCKING
  where the obligation assigns the root). A field a tree's hook mints is the hook's: none of its
  reads is declared.
- **Named, not minted.** What these rules leave concrete is a `DECLARATION_MISSING` DIAGNOSTIC row
  of `communication_gaps.jsonl.gz` (`ConfigRoots#gaps`, published with the declarations), its
  reason first in its detail: `CONFIG_KEY_UNRESOLVED`, a read whose key no literal names (`for (k :
  keys) conf.getInt(k, 0)`: a site is no key, and one symbol would stand for every key);
  `CONFIG_FIELD_OVERWRITTEN`, a field a constant store can leave holding the constant (`f =
  get(k); if (f <= 0) f = 1`: a plant would write a value the field never holds); and
  `CONFIG_READ_CONCRETE`, a read of a chosen key in another shape (a second field, another view,
  clamp or type, a getter beside the key's field).
- **Its reads left at the recording.** A plant stands where the key is minted: its field's declared
  reads, else its minted getter calls. Every other read of the key in the analysed scope (its
  application classes) -- a getter call in another shape or outside the slice, a read of another
  field holding it, a read of its field outside every region -- keeps the recording's value when a
  world moves the key (`ConfigRoots#keyRows`, over `#census`: JVM and catalog getters and the
  wrappers the recognition found; the getter calls a field's writers store are the field's own).
  The scope map states them, one `CONFIG_KEY` row per root (`sourceId`, `mintedAt`,
  `concreteReads`; `StaticScopeMap#configKeyRow`), and COMPOSE does not claim a witness moving a
  root that has any: no cluster holds that world (`compose/ClaimPolicy`, `UNPRODUCIBLE_ANSWER`
  DIAGNOSTIC). A key no read of which is planted (a field a tree's hook owns) has no row.
- **The world.** A configuration belongs to the world, not to an occurrence: the value an
  obligation assigns it is written at every read of its field, on every node, whatever occurrence
  runs it (`runtime/RootMint#configuration`), and planted at every getter return a symbolic
  occurrence reads. The VM label is the source's alone (`ConfiguredSourcePhaseContract#engineLabel`),
  so the reads of one key in one JVM are one symbol: a homogeneous cluster. That symbol holds ONE
  value: the first mint of the root in a JVM fixes it, and a later mint at another value -- an
  unset key's other default, another node's configuration -- is read concretely, an
  `UNSTATED_VALUE` DIAGNOSTIC row (`RootMint#configurationAgrees`); a second getter read of one key
  in an occurrence is the box its first read minted.
- **Domain.** A boolean is a MARKER, free over both values. An integral's domain is the hull of
  its anchors -- each getter call's literal default and `c - 1, c, c + 1` for each integral literal
  `c` a branch compares the value with within eight flows of the slice, never through a field, and
  no floor (`if (limit < 0)` flips at -1) -- mapped through its clamps (a planted value lies in
  their image: `Math.max(v, 1)` is never 0), and of the value the mint read: the declaration states
  the static hull, the mint row the whole (`runtime/ActiveRegion#configDomain`). A declaration stating half a
  domain or a bound that is no integer states none, named, and the root is pinned.

A tree may still call `CausynthSymbolicSource.symbolize(String sourceId, Object owner, String
fieldSignature)` (the Hadoop copy is `src/shim/java/org/apache/hadoop/ipc/CausynthSymbolicSource`):
the block-key trees' `HDFS.BLOCK_KEY.SERIAL_NO` and `EXPIRY_DATE*`, and hdfs-17960's
`HDFS.CONFIG.SNAPSHOT_DELETION_ORDERED` in `SnapshotManager.isSnapshotDeletionOrdered()`, on the
field this section's rules recognize as `CONFIG:dfs.namenode.snapshot.deletion.ordered`: the hook
owns it until its tree drops the hook.
`StaticSymbolicSourceDiscovery` finds the call by class simple name and signature and attaches one
declaration per source to every region that can run it (one hook site per source per region, else
refused). Its value is planted at a focused occurrence only, and its domain is the
`root-domains.jsonl` row for `sourceId` (absolute or `+k`/`-k` from the recording); without a row it
is pinned. A hook that runs in a case whose plan declares a phase of its source in no task (a
block key's serial in every NameNode of an unrelated check) mints nothing and is named by a
DIAGNOSTIC `DECLARATION_MISSING` row: its source is no root of that case
(`runtime/ActiveRegion#observeConfiguredSourceEntry`, `ConcolicTaskPlan#declaredPhase`); a hook
whose source the plan declares, run at a site its occurrence does not declare, still refuses
BLOCKING: a hook's plant is per site, so the value there stays unplanted. A configuration read at a
site its occurrence's catalog lacks (the recording never read the key there; a flipped path reaches
new reads) is not refused: the world's value is already in the field (`RootMint#configuration` writes
it at every read before the mint), so no symbol is minted, the read is stated as a concrete reading
(`SessionManifest#concreteReadings`), and a `DECLARATION_MISSING` DIAGNOSTIC row names it (that
occurrence's decisions on it are concrete). A claim moving the key stays producible.

Either way `runtime/RootMint#configuredSource` mints one symbol per source on the owner's
primitive instance field, keeps a propagated expression instead when the field already carries one
(`reused`), and its root row states the category, `CONFIG` or `HOOK`.

### 4.4 Admission

`plan/ConcolicScheduler.SymbolicInputSelection#decide` gives each proposed input one verdict:

| input | verdict |
|---|---|
| a clock's return, a configuration getter's return (`configSource`), a READ placeholder's own site, a `FAULT` marker | declared root: the replay mints (`DECLARED_SYMBOLIC_ROOT`; a clock also `DECLARED_WALL_CLOCK` = its tick) |
| a field a configured source of the region mints (a tree's hook, or the engine's configuration read) | `CONCRETE`, `CONFIGURED_SYMBOLIC_SOURCE_FIELD_OWNED` (the source mints) |
| a declared communication port (`COMMUNICATION_SITE_PORT`) | tracked, never minted (the attach installs the producer's value) |
| anything else | `CONCRETE`, `UNDECLARED_SYMBOLIC_INPUT` |

At the end of SEED (the recording's aggregation, `runtime/CausynthTraceRecorder`),
`causynth/RuntimeSelectedRegionFinalizer` plans the recorded occurrences the failure's demand
reaches, to a fixed point:

- **The question** `(r,c)`: the declared occurrence, resolved once against the target occurrences
  the recording observed (IDENTITY.md §9), and every target occurrence of its region and node whose
  context has its shape (`contract/ContextShape#sameQuestion`, over the recording's schedule,
  `RecordedMessages#shape`), at any index. A target occurrence outside it -- the same throw reached
  under another request or on another node -- is not the question's: no rule below plans it, so
  nothing only it would demand is planned either.
- **The demand walk** (`DemandWalk`), backwards over the candidate graph, one demand per (occurrence,
  cell), from the operands of the fatal guards the question's target occurrences decided; a demand
  is queued once and walked once, and a store site's writers and a decider's verdict are read once
  (a cell N occurrences read and M store queued the writers' guards N×M times: hdfs ad-hoc
  `TestFileTruncate`, 0.8 M duplicate demands of 2-4 KB each out of an 8 GB heap). Inside
  an occurrence it follows the edges of the methods its regions hold (its own and those folded into
  it) that ran in it (`observedMethods`): an edge of a method the occurrence never entered carried
  nothing there (ad-hoc `ReindexCollectionCmd-369`, Solr: along every method of their regions the
  target's 923 writers demanded 5134 more, along the methods that ran in them 244). At a cell a `WRITE_SITE` names it crosses, on the same node, to every activation that ran
  the storing method or took the arm of one of the store's guards away from it (a recorded
  `BRANCH` at that site in its calls, against the WRITE_SITE's `guardOutcomes`; any decision at a
  guard that is not binary) at a decision something the engine moves reaches there -- a tracked read (`READ_SITE`: the replay
  versions it, so another writer re-pairs it; an untracked stored read stays what it read), a root's
  dependency cell, an IN port's capture, backwards over the
  edges of the methods that ran in it (`DemandWalk#movable`; a decision the slice states no operand of
  is kept) --, whatever region it was performed under (`RegionDemandIndex#deciders`, `SHARED_LOCATION_DEMAND_V1`): a store on an
  arm the recording did not take is one flip away, so the closure keeps it, and a method that ran
  without reaching the guard, took its arm toward the store, or decided it on nothing a world moves
  is not (the last stated per region, a DIAGNOSTIC `ADMISSION_GAP`) (owner, 2026-10-02; the
  hdfs-bugs slowdisk-zero detector decides `max > 0` each turn and never ran the store of
  `slowDisksToExclude` behind it, an accessor's), and keeps the guards of the read locally; in a writer it demands
  the guards of the store, never the store's value (value provenance stops at a stored location:
  the values come from roots, below), nor the writer's own other writers.
  - **A heap location is one object's field** (Writers_W(l), GreyGraph §3.1): the recording names
    the objects each activation read or wrote a field on (`FIELD_OWNERS`, stamped by
    `runtime/RuntimeRegionPlanner#stampFieldOwners`: a field event's receiver, and the receiver of
    a call at a site that returns a field -- an unwoven accessor -- or mutates a field of its
    receiver -- a `WRITE_SITE`'s `declaredCallee` whose cell is not its carrier, an atomic's
    `value`: `RuntimeSelectedRegionFinalizer#fieldAccessingCalls`), and apart what a reference field
    held (`FIELD_REFERENTS`). A writer the recording saw access the field on other objects only than
    the reader did is not crossed to (`DemandWalk#holdsOthersOnly`): the holders for a store, the
    holders and what they held for a mutation through the field (a container's or an atomic's
    state); a referent shared by a store's holders is no shared location (Solr: every lambda
    capturing one ZooKeeper client, every DocCollection holding one cached `Integer`). A side the
    recording saw no access of the field on (a store on an arm it did not take, a static field's
    one location `0`) says nothing either way. hdfs ad-hoc `DataStreamer-638`: 1147
    `Configuration.get` occurrences ran the lazy store of `overlay`, on 10 objects; the reader read
    one.
  - **A message is one exchange leg**: at a cell the capture of a declared IN port names (an IN call
    return's assigned locals, any other's cut cell), in an occurrence performing a region that
    declares the port, it crosses to every occurrence whose capture of the port's export the
    recording bound to the same exchange leg (correlation, attempt and half:
    `RuntimeRegionPlanner#bindObservedCommunicationCaptures`) -- the other side of that one
    message -- and demands there the cells the export hands on (`WIRE_PRODUCER_V1`). A consumer the
    recording paired with no export (no exchange bound: a ZooKeeper read, a DataTransfer op on a
    tree without the op's envelope, IDENTITY.md §7.1) is a DIAGNOSTIC `ADMISSION_GAP` naming its
    cell and ports, and its value stays the one attached.
    No capture is admitted for being one: admitting every occurrence that captured a declared port
    planned 2673 occurrences for one ad-hoc check (`DataStreamer-1451`, round a40h).

  It records, per node, the locations it demanded and the objects it demanded them on, and the wire
  consumer cells it demanded. Every admission states its `demandDepth`: the hops of the shortest
  chain from the question that reached it (a target 0, a root's or a door's occurrence one past
  what it was found from).
- **Roots by relevance** (`causynth/RootRelevance`). A root read is a capture of a `CLOCK`,
  `FAULT` or `CONFIG` `DECLARED_SITE`; a configuration field's read (§4.3) is a configured-source
  phase, no capture, and plans with whichever occurrence another rule admits. Its influence is the
  forward reach of its `dependencyCell` over the candidate edges of the methods its occurrence
  performed -- value, guard and exception edges alike -- ended at a stored location (a cell some
  `WRITE_SITE` names) and at a wire producer (recording the consumer cell its `wire_handoff` names).
  The influence is static: the arm a root decides counts whether the recording took it or not (an
  expiry check that removed nothing), and a value leaving by a wire counts on the consumer's side. An occurrence one of whose roots reaches
  a location the walk demanded on its node -- unless the recording saw it access that field on
  other objects only (`Demanded#heldBy`) -- or a consumer cell it demanded anywhere, is admitted
  (`ROOT_RELEVANT_V1`, unless another rule admitted it), and every such occurrence seeds the walk
  with the cells on the root's way there, so what the root meets is demanded in turn (SOLR-18406:
  the commit's reservation a checkpoint's clock is compared with, and so the clock that set it).
- **Attached values by relevance**: an admitted occurrence's IN capture bound to an exchange leg is
  an input like a root. When its influence (from the cells its capture names) reaches what is
  demanded, by the same rule, it crosses its message as the walk does (`DemandWalk#crossMessage`)
  and seeds the cells on its way: the walk reaches an attach only where the attached value itself
  is demanded, and a value attached and then stored (hdfs-11741: the DataNode converting the
  KeyUpdateCommand's keys into the map its handshake reads) is found from the store it reaches.
- **Doors of a demanded message** (`RecordedMessages#doorsOf`): an occurrence that read a fault marker
  and sent, or took in, the message that started an admitted occurrence (its `Anchor`, else the
  message its turn took in, a DataNode's DataTransfer op; the recorded schedule's `SEND` names the
  sender, a `RECV` of the message a receiver) is admitted
  (`CONTROL_PRODUCER_V1`): its fault decides whether the message exists. These are the control
  producers EXPLORE proposes the faults of as flips (IDENTITY.md §7.3); the seven HDFS
  `MARKER_FLIPPED` witnesses move such an IPC door.

- **Equivalent deciders are one class** (`DemandWalk#classDeciders`). Occurrences the walk reached
  only as writers of a demanded store that stored no demanded cell in the recording (each left the
  store at a guard, or ran its method on another arm), on one node, in one region, under one context
  shape and call path (the index's sites), that did the same on the same state are one class while
  no one else accesses a cell demanded on that node between the first and the last
  (`causynth/RecordedAccesses`: every recorded field read and store, and every call at a store site
  that mutates through the call, `RuntimeSelectedRegionFinalizer#storingCalls`, or at a site that
  returns a field, each with its seq, its call and whether it stored). "The same" is one
  `signature`, stamped by the aggregation (`runtime/RuntimeRegionPlanner#stampSignatures`): a digest
  of the occurrence's events in recorded order -- the methods entered and on which object, calls
  with their arguments and returns, decisions with their outcomes, messages by exchange leg, and
  each field access with its object and value and, for a read, its version: the count of recorded
  stores of that (field, object) before it (`FieldAccessEvent#version`). Equal counts mean no
  recorded store between two reads, so one version, the one the replay pairs them with; the value
  rides along because a store the weave does not record (a JDK body's) moves no count. A flip query
  is a function of what its occurrence read and decided, so the members ask one query; the store a
  flip enables lands where its member ran, and with nothing else touching a demanded cell between
  them every reader and writer meets it in the same order, so COMPOSE pairs any member's store as it
  pairs another's. The first member is planned, at the class's shortest chain, and states the class
  (`deciderClass`: `members`, `first`, `last`); the others are not. Never merged: a recorded store
  of a demanded cell (a version a reader may have read), an occurrence the walk reached in any other
  role (a target, a wire producer, a root's or a door's admission), one that captured a
  DECLARED_SITE minting a root (an `inputKind`: a clock, a fault marker, a configuration getter, a
  READ placeholder), or one that attached or exported a message value. hdfs-adhoc-16: 1218 to 1520
  polling turns of the block scrubber, each leaving `removeBlock`'s store at its guard and running
  `run()` (the iterator's store) past its own, were one job each and cut at PLAN; offline on its
  DS5/SS5 recordings 1168/1191 turns fall into 33/32 classes and PLAN plans 110/91 occurrences with
  no cut.

A root read none of this reaches is not planned: its occurrence runs concrete, unless another rule
admits it. PLAN schedules what this admits up to `schedule_max_jobs`, keeping the nearest demand
depths that fit whole (PIPELINE.md §3).

### 4.5 Randomness is not a root

The weave replaces `new Random()`, `Math.random()`, `Collections.shuffle(List)`,
`UUID.randomUUID()` and `ThreadLocalRandom.current()` in both passes with `runtime/Randoms`, so a
replay draws what the recording drew. `ThreadLocalRandom.current()` becomes `Randoms#current`, a
`Random` seeded by the same key, and each draw on what it returned becomes that `Random`'s (a bounded
draw only `ThreadLocalRandom` declares, `nextInt(int,int)`, `nextLong(long[,long])`,
`nextDouble(double[,double])`, a `Randoms` stand-in of that name), only where every use of the value
is such a draw or stands where a `Random` may (a return, an assignment, an argument); any other use
leaves the site as written, counted and named in the weave's log (`CausynthPipeline#seedThreadLocalRandom`).
The draws are one list (`plan/WorkStartSites#UNSEEDED_DRAWS`), which the lineage scan keeps a class for. HDFS's block placement picks
a pipeline's DataNodes through NetworkTopology's `ThreadLocalRandom`: hdfs-adhoc-42's replay wrote to
dn0 first where its recording wrote to dn2 first, and every DataXceiver turn after took another
node's slot.
A draw is keyed (`Randoms#key`) by its endpoint where it runs in an occurrence with a context (a Root
or an Anchor) inside the window: the same function of the same inputs in both passes. Anywhere else
-- before the window, or in a Lost context, whose address siblings share (unnamed work, a turn begun
before the window) -- it is keyed by the thread's node, the starts it was handed on through
(`Identity#handoffs`, as a schedule event's context is), its site, and its count under that key, the
counts restarting at each window: hdfs-adhoc-01 (round HS1) started a cluster inside the window while
no hop stood, its DataNodes all drew one endpoint's UUID, and their registrations refused each other
for the rest of the run. A key one thread alone draws under counts in that thread's program order,
the same in both passes: a cluster whose nodes are named from their construction (the adapters'
node startups, IDENTITY §5) keys each DataNode's draws by its node. Threads that share a key
(unnamed work of one node started under no hop: HS1's DataNodes, all `workload/unregistered` on a
tree without node startups) take its counts in the run's arrival order, so two runs may hand them
each other's values: distinct is what is guaranteed there, not equal. A key's bits are
mixed into the seed (`Randoms#seed`): neighbouring counts of one site would otherwise start
generators nearly alike (alike UUID prefixes, one pick of four for every count).

### 4.6 Root demand

`causynth/RootDemand` asks where the values the declared throw's path guards decide on enter what
the slice follows. Backward from the operands of the guard edges (`exception_guard`,
`guard_dependency`) at the TARGET_SITE's guards, its chain -- the calls into its method up to
its execution context's entry included (§3) -- and the chain's deciders (`Site#pathSites`), over the candidate edges, nearest
first, every path stops at its first *boundary*, at most sixteen edges out; a receiver edge
(`accessor_receiver`, `method_receiver`, ...) names which object is read, not the value, and is
followed only to a value-like receiver (a box, a `String`). The classes:

| class | the boundary | what the demand does |
| --- | --- | --- |
| `CLOCK` | a clock's return (§4.1) | nothing more: it is declared |
| `FAULT` | a fault marker's return (§4.2) | nothing more: it is declared |
| `CONFIG_CALL`, `CONFIG_FIELD` | a configuration (§4.3) | the twelve nearest keys within sixteen edges are minted, and twelve more at the writers' guards (below) |
| `READ` | a JDK atomic's value | a chosen read is a READ placeholder (§5.4) though only its own region stores it |
| `TRACK` | an integral or boxed field a region stores | a chosen read is a READ_SITE (§5.1) however many flows from a branch |
| `TRACK_IDENTITY` | a reference, `String` or enum field a region stores | a chosen read is a READ_SITE as well; its value is never freed (R3) |
| `TRACK_CONTAINER` | a container's state (a field of a container type, a container query's return) | a chosen field read is a READ_SITE as well; its state is never freed (R3) |
| `PRE_WINDOW` | a field no region of the slice stores | chosen, first in scope growth (§2.4): a writer out of scope (a configuration holder's constructor) may store it |
| `WIRE` | a region root's formal: what a message or a thread start hands over | named (R2) |
| `IO` | a stream, file, socket, channel or native result | a demanded door where its outcome reaches the slice (below), else named (`NO_DOOR`) |
| `SCOPE` | a call into the system's own code outside the scope, a formal no caller in scope passes | chosen, first in scope growth (§2.4) |
| `LIBRARY` | any other library result | named |
| `CUT` | a path still open sixteen edges out, no boundary yet | named |

Of each class the twelve nearest boundaries are *chosen* (a cell per boundary); every row states
why it is not (`cut`: `WIDTH`, past the twelve nearest of its class; `DISTANCE`, past sixteen edges,
every `CUT` row and a configuration key measured beyond the bound on the cone; `NO_SOURCE`, a
configuration no source declares, a `String` getter). A configuration
belongs to the world: it is read in whichever occurrence wrote what the anchor reads, beyond the
boundary between them (hdfs-17960's key stands behind the `READ` of `numSnapshots`, in the edit-log
replay that decremented it), so its keys are measured on the whole cone (every edge, no boundary
stops it), a field's at the field, a getter call's one past the local it lands in. Whether a
writer of a tracked read ran decides what the read saw, so the keys are measured again on the
cone from the guards of the writers of each chosen `TRACK`, `TRACK_IDENTITY`, `TRACK_CONTAINER` or
`READ` read (the guard rows into its cell: the store's own branches and those of the calls into
its method, §2.2), each one edge past the read; of the keys the path's cone did not choose, the
twelve nearest within sixteen there are minted too, so a key near a writer never displaces one
near the anchor. Each configuration row states the cone
it was measured on (`measured`: `PATH`, `WRITERS`); a row is chosen when its key is. A named class
is a row, never a freed value: freeing it would invent a value no execution produces.
**Local file faults.** A local file operation is a door (§4.2) only where its result or its
failure flows into what the walk demanded (`RootDemand.Faults`, `causynth/LatentFaults`):

- (a) `VALUE`: an IO boundary of the walk whose call returns a failing result (`File#renameTo`'s
  false) into the path;
- (b) over the latent model (`FaultPropagation#latent`: the woven program plus, where no door
  stands yet, each call of a throwing row's anchor, each checked throw on a failing-result
  anchor's failing arm, and each call into the system outside the analysed program declaring a
  checked exception), a fault that escapes its method from a point before a demanded store
  (`ESCAPE`: a writer of a chosen TRACK, TRACK_IDENTITY, TRACK_CONTAINER or READ field), or that a
  handler catches whose arm decides a site the walk followed an edge at (`HANDLER`: a site on the
  target's path only where the handler leads to it; a fault that only leaves before the throw
  removes it), followed down the calls it escapes to the call it comes from.

Its distance is the site's plus one plus the calls it escapes. The doors this pass wove stay; the
nearest calls are added until twelve stand (rows `fault_escape`, `fault_handler`, `door`, the
others cut `WIDTH` or `DISTANCE`), and `io_doors.jsonl` holds them for every later pass, each with
its `via`: the methods the descent walked, from the demanded site's method down to the door's
caller. A demanded door roots no region, unlike a catalog door at calls: its marker is read in the
occurrence that runs the demanded site, the chain's methods joining every region that holds the
site's method (`causynth/SymbolicRegionPlanner#fold`; no root is added, so no address moves). Rooted
as fault entries, utility callers (`StorageInfo#readPropertiesFile`, `FileUtil#listFiles`) opened
occurrences wherever they ran, and the test thread's DataNode starts lost their hop
(hdfs-adhoc-26, `DECLARED_TARGET_BEFORE_WINDOW`). A call whose demanded site no region holds is cut
`NO_REGION`. A call
into the system outside the scope where such a fault could stand is an IO frontier row
(`fault_frontier`): the twelve nearest join scope growth's demanded rows (§2.4). `run_engine.sh`
`campaign_analyze_grown_scope` runs the static pass again while it chooses more doors, outside
the growth budget (a door moves the unit indices of its method, so the scope map is the woven
body's).

`root_demand.jsonl` lists every boundary (`class`, `distance`, `cell`, `siteId`, `edgeKind`,
`chosen`, `cut`, `measured`); every DECLARED_SITE and READ_SITE the demand reached states its `demandDistance`.
That mark is the static half of a concrete anchor's demand: an anchor every admitted path decided
on no symbol demands the reads its deciding predicate names (by read event: a compound guard's later
tests read after the target row) and the reads it made before it decided that carry it
(`explore.ClosurePlanner#concrete`, `StaticScopeMap#demandedAt`; PIPELINE §7.2), their writers
asked as a symbolic predicate's are.

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
    one too (`static: true`: its location is its class's). A field only its class's construction
    stores (`#constructionOnly`: final, or private and stored only by its own class's
    constructors, `#storedOnlyAtConstruction`: Lucene's `IndexFileDeleter.refCounts`, a lambda's
    captured value) is no `REFERENCE`: its only writer is its constructor, so the field itself has
    nothing to re-pair. The same rule marks a store into such a field `constructionOnly` (§5.3);
  - `CONTAINER`: such a construction-only field holding a map, set, list, queue or deque
    (`smt/JavaContainerTypes#shape`; an array is none, its elements being locations of their own):
    its reference never changes, but the container's contents change in place, through `put`,
    `remove` and the like from other threads, and they are what a query reads
    (`BlockTokenSecretManager.allKeys`, `BlockPoolManager.bpByBlockPoolId`,
    `DirectorySnapshottableFeature.snapshotsByNames`). The location its reads and mutations name
    is the container's state (VM.md §6), observed as §5.2 says. Any other construction-only field
    is none (hdfs-adhoc-03's `FSOutputSummer.sum`, a `DataChecksum`);
- decides a branch: the read's value reaches a branch operand within eight flows
  (`StaticScopeMap#decidingCells`, `DECIDING_FLOWS`), never through a field and never across a
  `wire_handoff` edge, or the root demand chose it, a `TRACK`, `TRACK_IDENTITY` or
  `TRACK_CONTAINER` boundary of the throw's own guards however many flows away (§4.6); a read that
  only feeds data stays untracked. A `CONTAINER` read is tracked only where the root demand chose
  it: every query of a container reaches a branch, so the deciding rule would track every final
  cache a configuration parse reads and make its region record from entry (hdfs-adhoc-28's seed:
  `Configuration.CACHE_CLASSES` and `REGISTRY`, `WeakHashMap`s no model knows, took the DataNode
  startup region from 13 to 262 recorded decisions);
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
atomic's RMW call, before the `getfield`, and before the call of a read through an accessor, on the
call's receiver: such a `READ_SITE` (an `accessor_field_return` edge) names the accessor as its
`declaredCallee`, and as its `vmSite` the accessor's body, where the VM records the read, so a
recorded read joins its carrier there (`StaticScopeMap#carriersAt`, `#demandedAt`) (hdfs-bugs slowdisk-zero: `FsVolumeList.chooseVolume` reads `slowDisksToExclude`
through `DataNodeDiskMetrics.getSlowDisksToExclude()`, and its read had stated no version). Inside an active region it calls the VM's
`observeField(owner, declaringClass, name, descriptor)` (`runtime/ConcolicVmBroker#observeField`),
which starts the location's log with an INITIAL version holding the current value -- an integral's
or a wrapper's word, a reference's identity -- unless a log stands (VM.md §5). A concrete store
after it is then a version, and a read states the version it saw, INITIAL when no store of the
window came first; the INITIAL is a write row of its own (`contract/WriteRow#initial`). An access before its object's constructor call, and a read site that is neither a `getfield` of
its cell nor an accessor's call, are left unobserved; a status the VM refuses with (`UNSUPPORTED_TARGET`
for a `float` or `double` field) is an `UNSTATED_VALUE` DIAGNOSTIC row naming it.

Each observed row states its cell's `trackedKind` and what it observes: `field`, the cell as above;
`container`, the state of the container the cell holds. A `REFERENCE` cell's access is observed
like a value's; a static cell's (`static: true`) on its declaring class's mirror, the key its
location has (`CausynthPipeline#instrumentConcolicObservedSites`), before the `putstatic` or
`getstatic`. Not observed: a `publishedFrom` write site, whose receiver is the local's container,
not the carrier's holder (its log starts at its first model event).

**A container a cell holds** (a `REFERENCE` or `CONTAINER` cell of a container type, no array) is
observed by its state: after each read of the cell, on the referent the read returned, and before
each container mutation through it, on the call's receiver (a view or an iterator stands for its
container), `ConcolicRegionRuntime.observeTrackedContainer(siteId, cell, container, afterMutation)`
calls the VM's `observeContainer` (`runtime/ConcolicVmBroker#observeContainer`, VM.md §5.4), which
starts the container's state log with an INITIAL stating what it holds, unless a log stands. Every later
modeled mutation is then a `STATE` version with its writer, site and guard -- whatever object
reaches the container (VM.md §6) -- and every query reads one, so COMPOSE re-pairs the anchor's
query of it like any state read (PIPELINE §8, `SmtLowering#movedQuery`): to the INITIAL, or to an
earlier or later concurrent writer's state. Before, a container whose contents stayed concrete had
no log (the VM starts one only at a symbolic value or a guarded mutation): hdfs-adhoc-11's
`allKeys.get(keyId)`, -28/31's `bpByBlockPoolId.get(bpid)` read no version, so nothing was there to
re-pair; the block-key cases had theirs only because a wire-carried key or a clock-guarded removal
reached the DataNode's map first. A `CONTAINER` cell's field is never observed (its constructor's
store neither), and a mutator call never observes a field -- but an atomic's write of its value: its
receiver is no holder of the cell (a `GSet`'s `put`, a `BestEffortLongFile`'s `set` had each
access refused `HANDOFF_FIELD_NOT_FOUND`); a mutator call on a cell holding no container observes
nothing. Outside every region a mutation runs as bytecode no model sees, so a second observation
just after it marks a standing log incomplete (`UNHOOKED_CONTAINER_MUTATION`) instead of leaving its
chain stale -- after, so a log another thread started meanwhile is marked too. A value
no container model knows (a `TreeMap`, a `CopyOnWriteArrayList`) is an `UNSTATED_VALUE` DIAGNOSTIC
row naming its class, once per site.

Every observed `READ_SITE` access is a read row, whether or not a published expression holds its
value: the VM's read log states each read's chosen version (VM.md §5.2), and `runtime/RowPublication
#loggedReads` publishes every logged read in the method of a `READ_SITE` (its `vmSite`, the map the
replay reads with its guarded-store table) through the read path an expression's read node takes,
so a read both state is one row. Before it a read whose value reached no expression -- a reference
compared with a constant (hdfs-adhoc-45's `state == State.IN_SEGMENT` in `FSEditLog.isSegmentOpen`),
a value handed to a call the VM does not model -- was no row, and neither the closure nor a STATE
family saw it. A read log the VM cut at its 1024-read bound is an `UNSTATED_VALUE` DIAGNOSTIC, and so
is a logged read of a version the location's log does not list: it would pair with nothing.

An occurrence of a region that reads a tracked cell records its branches from region entry
(`SymbolicInputSelection#readsTrackedState`, `StaticScopeMap#trackedRegions`).

### 5.3 Guarded stores

`runtime/GuardedStoreSites#install` hands the VM one line per guarded `WRITE_SITE` store
(`methodKey`, the store as the VM names it -- `CALL <name>` from `declaredCallee`, else `FIELD
a/b/C.f` from `cell` -- then its guard site ids, tab-separated), from the map named by
`CAUSYNTH_STATIC_SCOPE_MAP`; a missing or refused table fails the session by name
(`GUARDED_STORE_SITES_*`). A `constructionOnly` store is none (§5.1): a concrete store there starts
no log, so the field names no owner its readers project through; a symbolic store into it is still
logged by value (VM.md §5.1). hdfs-adhoc-03's `FSOutputSummer.sum` (a final `DataChecksum`, its
constructor's store guarded by `newStreamForCreate`) had made every read of it a guarded reference
read and every chunk's CRC ~10k symbolic nodes. The VM uses it to version a concrete store at a listed site made after
one of that site's guards decided symbolically (VM.md §5.3). A `publishedFrom` write site's guards
join its store's line: SOLR-18406's `updateKnownCommitPoints` lists the `isDeleted()` branch its
`map.put` runs under (`CALL put`).

### 5.4 READ placeholders

A `DECLARED_SITE` `ACCESSOR_RETURN` whose accessor runs outside the woven program (not an
application method) and whose cell some other region stores -- any region, where the root demand
chose the read (§4.6) -- becomes `inputKind: READ` (`StaticScopeMap#markReads`). Keyed by site and cell (`#readSites`, `#readKey`), since the cell
alone (`AtomicInteger.value`) names every object of its type. The replay mints a placeholder there
(`runtime/RowPlaceholderMint`) that the closure binds to that location's writers.

### 5.5 Writers of a read

For a demanded read, `explore/ClosurePlanner#writers` asks the session's rows for eligible writers
and the map for the static write sites of the read's carrier (`#carriersAt`, `#writersOf`), on the
reader's node only, held by an occurrence that may hold the read's object: one whose recorded
accesses in that session name owners, none of them the location's, holds other objects only and is
no candidate (Writers_W(ℓ) is per object: every state watcher's parse builds its own `Slice`s). A
recorded site's type matches a map row's by sort, or by the value it holds:
a wrapper location agrees with a row of its primitive (a stored box states its value) and with a
reference row (a stored null) (`StaticScopeMap#sameType`). A reference row states its object's
runtime class and the map row the carrier's declared type; with no class hierarchy at hand they
agree where the cell may hold the class (`#mayHold`): the same class, or value sorts that agree (a
container's shape by interface, `JavaContainerTypes#shape`; a String; a box's value). A declared
class no sort names (an application class, an interface, `Object`) holds any reference; a runtime
class no sort names may be a container, never a String or a box, both final. A `Map` field holding
a `ConcurrentHashMap` is that field's carrier. The site must also store the recorded location's
kind (`#stores`): a field store, or an atomic's write of its value, a field -- a static one a
class's location, an instance one an object's; any other mutator call
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

`communication-mappings.jsonl` (`-Dcausynth.communication.mappings`, from
`causynth_communication_mappings`) holds WIRE_FLOW rows; a
row of any other kind (a DOOR row: doors are the library catalog's, §4.2) is refused:

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
first demanded getter. The rule does not read the doors: which transport serves a proxy is
decided at run time, where no static pass follows it. A message no service reaches (an fsimage
section, an edit-log record, a DataTransfer op) is written to a file or a stream that no door
carries values over, and derives no port.

The rule is by type. A message that an RPC carries and a stream also writes (`ExtendedBlockProto`,
in `LocatedBlockProto` and in a DataTransfer op header) exports at every setter call, including one
whose message never reaches a door. A DataTransfer op is itself a message (IDENTITY.md §7.1): the
leaves of such a type in its header and fields cross with it, so the block a DataNode decodes from
an op is paired by handle with the export of the client or the upstream DataNode that sent it, and
the recording binds both captures to the op's leg, which the walk crosses (§4.4); the DataNode's
turn keeps its own address. The op's own messages (`Op*Proto`) still derive no port.

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
A refusal is its frame's: the paths and arms whose closure reaches an occurrence its session filed an
`UNSTATED_VALUE` row on compose with the constants its rows state, and name the frame
(`compose/Composer#frames`, a `Composer.Concrete` FRAME).

## 7. Current limits

- Roots are clocks recognized by the call-return rule, the library catalog's door faults (no door
  on a read, §4.2; a local file door only at a demanded call, §4.6), configuration (§4.3) and tree
  hooks. A clock read through a field, a parameter,
  `java.time`, or an interface whose implementation is outside the scope is not recognized;
  pre-window state is a root only where a tree hook says so.
- Configuration reads left at the recording (§4.3) are counted over the analysed scope only: a read
  in a class outside it, a read whose key no literal names, and a minted getter's return in an
  occurrence a replay runs concretely are not, so such a world can still be claimed (and CONFIRM
  then runs it as planted).
- Configuration (§4.3): one symbol per key per JVM, a homogeneous cluster, by design; a node read
  at another value than the JVM's first is read concretely. The VM names a field mint by its
  owner's class, so one key is minted in one shape, at one field (the first by signature) or, with
  none, at its getter returns, and every other read of the key -- a second field caching it, a
  getter beside its field, another view, clamp or type -- is read concretely
  (`CONFIG_READ_CONCRETE`): a world that flips the key leaves those reads at the recording's
  value. A field declared in a class two runtime classes extend mints one symbol per class. A
  static field, a `float` or `double`, a box, a `String` or an enum is no root (an enum or `String`
  key would need a finite-set domain, so a String key is minted under one view, a boolean),
  nor a value computed from a configuration by arithmetic, nor a value whose key no literal names.
  A domain is bounded by clamps only: a field the constructor validates (a throw on a bad value)
  can be planted with a value the validation would refuse. A getter's return is planted only where
  a symbolic occurrence reads it, a field at every read of it.
- A functional argument is entered only where the call that takes it is demanded and its class is
  the one it was created from: one read from a field or a parameter states no class, and a `forEach`
  (no result to demand) enters nothing. A callback's body is still reached through the fields it
  writes (field-writer expansion over its method) and its captures through the constructor-object
  edges, but its parameters -- the receiver's elements or entries -- are not bound to the receiver
  (no edge from a library call's receiver to the functional method's formals).
- Root demand (§4.6) is chosen once, at SEED: no re-seed admits a boundary the seed left unminted
  or untracked. Its classes read the slice's edges, so a value the slice never reached is no
  boundary, and a concrete anchor's demand joins a read row to a demanded read by its method, kind
  and type, not its bci (`StaticScopeMap#demandedAt`).
- The VM versions integral instance fields, wrapper fields, `REFERENCE` cells (reference fields
  and `AtomicReference.value`, a static one on its class's mirror), the atomics' integral
  `value` and the state of a container a cell holds (`CONTAINER` cells included) from an observed
  access (§5.2). A container reached through a
  replaced reference is the referent's state its store stated (`referentState`), which COMPOSE
  asks per candidate (PIPELINE §8). Not tracked: `float`/`double` fields, static values, `String`
  fields, array elements (a construction-only array field's elements included), and containers
  the VM does not model (`TreeMap`, `TreeSet`, `CopyOnWriteArrayList`; classified by interface
  here). A mutation of an observed container by a thread outside every region is detected only at
  the slice's mutation sites of its cell; one through an alias the slice does not name is not. A `String` field's log
  starts at its first symbolic store, with no INITIAL (VM.md §5.1), so a store before it -- a null
  -- is no writer a read of it can be re-paired with (open defect 34).
- Root admission (§4.4) is by field, not by object: a root whose influence stores a demanded
  field of another object is admitted. It sees a root's effect only through the candidate edges
  of the methods its occurrence performed: an effect that leaves through a call outside them, or
  through a location no `WRITE_SITE` names, is not seen. A fault reaches a planned occurrence only
  as a door of the message that started it, so a door fault whose message started no planned
  occurrence (one EXPLORE meets only as a member of a task's state-connected factor) stays
  unplanned. The walk does not cross a wire: a value's provenance on the sending node is walked
  only from a declared port's capture and through a root's influence.
- A library call's receiver enters `S` only when it is shared state in the calling method (§2.2):
  a receiver passed in as a parameter is the caller's to demand, and is not followed up.
- Control dependence follows only door faults a handler catches; any other exception edge is
  ignored (a demanded file fault that escapes before a store is chosen by the latent model, §4.6,
  but no edge states it: the writer is planned as the store's writer). A fault reaches a caller only through the analysed program: a protocol call of a class
  outside the scope (HDFS's `*TranslatorPB`, whose RPC engine invoker is out of scope too) raises
  nothing, so the IPC doors of the named HDFS cases stay outside their callers' slices. A program
  exception (`throw new` of a non-door kind, e.g. `RecoveryInProgressException` from
  `FsDatasetImpl.initReplicaRecoveryImpl` caught in `recover()`) is no fault branch, and a
  precondition helper that throws decides nothing at its caller. Across calls it follows the
  activation of the target's method and of a method holding a demanded store or mutation, three
  calls up (§2.2), and write-site guards; it never crosses a thread start, an executor submission
  or the wire.
- Derived ports cover only scalar getters of protobuf messages a protobuf service carries, with a
  setter call in scope: no repeated, enum, `bytes`, nested or map-keyed fields, no string codecs,
  no frames, no message of a transport without services (DataTransfer ops, HTTP bodies, ZooKeeper
  nodes). `String`, boxed and reference leaves get no `v_H`. Every other cross-process value needs
  a declared row.
- Growth is capped by `causynth_scope_growth_budget`, spent nearest-first on every class a row
  resolves to (all CHA implementations), and never reaches classes outside the lineage roots.
