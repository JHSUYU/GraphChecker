# The concolic VM

A customized OpenJDK 8 Zero VM keeps a symbolic expression beside the concrete value of every
operand-stack slot, local and heap location, versions shared locations so a read can name its
writer, and hands expressions across communication boundaries. Replays run on it; the recording
runs on a stock JDK 8 (`experiments/lib/execute.sh`).

Paths: `VM/` = `third_party/OpenJDK-Concolic-Execution-Engine/hotspot/src/share/vm/`, `BI` =
`VM/interpreter/bytecodeInterpreter.cpp`, `SFV` = `VM/concolic/sharedFieldVersions.{hpp,cpp}`,
Java paths under `src/main/java/edu/uva/liftlab/graphchecker/`.

## 1. Build and use

- Build: `third_party/OpenJDK-Concolic-Execution-Engine/scripts/causynth_build_in_docker.sh`
  (GCC 6, boot JDK 8, libffi in the image); the image lands in
  `build/linux-x86_64-normal-zero-release/images/j2sdk-image`. All concolic code is under
  `#ifdef ENABLE_CONCOLIC`.
- Use: `custom_jdk_home` (`CAUSYNTH_CUSTOM_JDK_HOME`) names the image; `run_engine.sh
  campaign_freeze` refuses a campaign without its `java`, `rt.jar`, `libjava.so` and `libjvm.so`
  and digests them into the run manifest. `execute.sh` starts replays on it.
- The Zero C++ interpreter is the only execution engine; the smoke tests run `-Xint`.

## 2. Shadows, sessions, regions

- **Object identity.** Every object carries an extra header word `_sym_rid` (`VM/oops/oop.hpp`);
  it survives GC and is reset at every allocation path. Heap shadows (`SymInstance`, `SymArr`,
  container states) live in the session heap keyed by it (`VM/concolic/sessionSymbolicHeap.cpp`).
  Interned strings get a detached shadow, never the shared object's.
- **Stack shadows.** One `ThreadContext` per thread (`__thread`, `VM/concolic/concolicMngr.cpp`)
  shadows operand slots and locals; arguments and returns move through `ShadowStack` at every Zero
  frame push and pop (`VM/concolic/shadow/shadowStack.cpp`).
- **Session.** `openWorkloadSession` / `closeWorkloadSession`: one per workload JVM. Every
  expression is allocated in one session arena (`VM/concolic/globalSymbolicSession.cpp`) and freed
  at close; one event clock numbers versions, reads and region entries (`currentSymbolicEventId`).
- **Regions.** `startConcolicRegion` / `finishConcolicRegion` bracket one activation on one thread;
  each region frame owns its guard, auxiliary conditions and branch events
  (`VM/concolic/threadContext.cpp`). Nothing is recorded in a region until it reads something
  symbolic (the admission gate); `observeExactPrimitiveField` and every mint open it.
- **Branches.** The weave marks decision sites with `markConcolicBranch(siteId, ...)`; a marked
  branch is an event even when concrete (zero conditions). `getConcolicBranchEvents` returns the
  events since the last read; `getConcolicPathConditionRange` a range of the region's conditions.
  `pauseConcolicPathCondition` / `resumeConcolicPathCondition` (nestable) mute recording around the
  engine's own code.

## 3. Propagation through bytecode

| bytecodes | behaviour |
|---|---|
| constants, `new` | push no expression |
| loads, stores, `iinc`, stack ops | move the shadow |
| int/long/float/double arithmetic, `neg`, shifts; the 15 conversions (`TypeCastExpression`) | build the expression; `iand`/`ior`/`ixor` over booleans become `&&`, `\|\|`, `!=` |
| `lcmp`, `fcmp*`, `dcmp*`, `if*`, `if_icmp*`, `if_acmp*`, `ifnull`/`ifnonnull` | branch conditions |
| `tableswitch`, `lookupswitch` | the taken case; the default arm is the conjunction of `sel != k` over every key |
| array loads/stores, `arraylength`, `newarray`/`anewarray` with a symbolic length | INDEXED read/write over the array's container state; a symbolic index records `idx >= 0 && idx < SIZE`; a load at a concrete position the recorded writes decide builds no READ (§6) |
| `getfield`/`getstatic` | the field shadow, resolved through the version log where tracked (§5); a demand-minted `FieldAccessExpression` where the owner is shadowed |
| `putfield`/`putstatic` | set the field shadow; publish a version (§5) |
| `invoke*` | argument and return transfer; model dispatch (§4) |
| `Method.invoke`, `Constructor.newInstance` | boxed arguments and result carried (`VM/runtime/reflection.cpp`) |
| `checkcast`, `monitorenter`/`exit` | concrete |
| `instanceof` | concretized: no condition |
| `multianewarray` | dimension expressions dropped |
| exception unwind | shadows cleared |

## 4. Calls and library models

`VM/concolic/methodSymbolizer.cpp` intercepts a call when the callee's holder class name equals a
registered model, a boxing class, or a muted prefix (exact name: a subclass of a modeled class is
not modeled). Any other Java callee is interpreted and propagates normally. A native with a
symbolic argument returns a concrete value, except `Unsafe.get<Primitive>(Object, long)`, which
returns the field shadow at that offset (`VM/concolic/native/nativeGetPrimitiveHandler.cpp`).

**Muted subtrees** run concretely and return no expression: `org/slf4j/`, `org/apache/log4j/`,
`org/apache/commons/logging/`, `java/util/logging/` (observation only), `com/sun/crypto/provider/`,
`sun/security/provider/` (one-way functions), `sun/misc/Unsafe`, `sun/instrument/TransformerManager`,
Jackson's `UTF8JsonGenerator` and `BeanPropertyWriter` (`VM/concolic/reference/symbolicMiscObjects.cpp`).

**Models** (`VM/concolic/reference/`):

| class | modeled | not modeled |
|---|---|---|
| `String` (entered only with a symbolic operand) | `charAt compareTo concat contains endsWith equals equalsIgnoreCase hashCode indexOf isEmpty lastIndexOf length matches regionMatches replace* split startsWith substring toLowerCase toUpperCase trim valueOf ...`; results are string operations | `toCharArray`, `getBytes`, `getChars`, `new String(bytes/chars)` return no expression |
| `StringBuilder` | `append` (as concat), `toString`, `length` | `insert delete deleteCharAt replace reverse setCharAt setLength` leave the builder's expression unchanged; `StringBuffer` |
| boxing `valueOf`, `new X(v)` for `Boolean Byte Character Short Integer Long` | the box's `value` shadow on the returned object | `Float`/`Double.valueOf` |
| `Integer.toString(int)`, `Integer.toString()` | string of the int | other primitive-to-string conversions become a named `unsupportedPrimitiveStringConversion:` operation |
| `Integer.parseInt`, `Long.parseLong` | a method-return symbol stating its concrete value, plus a `MethodExpression` condition | |
| `BigDecimal` | 8 signatures | `<init>(double)`, `<init>(String)` mint symbols unrelated to the argument; `BigInteger` |
| `AtomicInteger`, `AtomicLong` | `getAndIncrement getAndDecrement incrementAndGet decrementAndGet getAndAdd addAndGet compareAndSet weakCompareAndSet` as read-modify-write versions, when the receiver is shadowed | `set lazySet getAndSet accumulate*`; `AtomicBoolean`, `AtomicReference`, `LongAdder`, atomic arrays, field updaters |
| `HashMap`, `LinkedHashMap` (views, iterators, entries) | `put get remove containsKey isEmpty clear size entrySet keySet values iterator hasNext next getKey getValue`, conditional removal | `putAll putIfAbsent replace replaceAll compute* merge` abandon the state; `Entry.setValue` abandons the entry |
| `ArrayList`, `ArrayDeque`, `AbstractList` iterators | list and deque operations | `removeIf` abandons |
| `HashSet`, `LinkedHashSet` | set operations | reads are not bound to versions |
| commons-lang 2 and Spring `StringUtils` | `isNotBlank`, `isEmpty` | commons-lang3 |

Every other collection (`ConcurrentHashMap`, `TreeMap`, `TreeSet`, `LinkedList`, `CopyOnWrite*`,
`PriorityQueue`, blocking queues, `Hashtable`, `EnumMap`, `Collections.*` wrappers) is interpreted as
plain objects: its elements' fields propagate, but it has no container state and no version log.

## 5. Shared-state versioning

`SFV` keeps a version log per location `(ownerSymRid, slot, kind)`, kind `INSTANCE_FIELD`,
`STATIC_FIELD` (owner = the class mirror), `ARRAY_ELEMENT`, or `MAP_STATE` (a container's whole
state, slot `-3`; a view and its map are one location). Version kinds: `INITIAL`, `WRITE`, `RMW`,
`STATE`, `UNOBSERVED`. A version carries its expression, writer, site, path guard and, for a
scalar, the concrete word the store left.

### 5.1 When a location is tracked

Tracking is by value; nothing is declared in advance. A log starts at the first symbolic store, a
mint, an attach, a symbolic container operation, or `observeExactPrimitiveField` (§5.4). Once
tracked, every store to it is versioned, concrete ones included. A version is published after the
concrete store completes, with the stored operand, not a heap re-read.

### 5.2 Reads

A read of a tracked location resolves to the newest retained version and states the word it
loaded. When the newest scalar version's word differs from the loaded one (a write the hooks never
saw: another thread outside every region, `Unsafe`, reflection), the read publishes an
`UNOBSERVED` version holding the loaded constant and permanently clears `writerSetComplete`.

### 5.3 Guarded concrete stores

The session's guarded-store table (`installGuardedStoreSites`, from `runtime/GuardedStoreSites`)
lists methods with control-dependent stores and their guard branch sites. A container mutation
(`put`, `remove`, `clear`, `add`, `offer`, `set`) in a listed method, after one of its guards
decided symbolically on this path, publishes a `STATE` version and starts the container's log
(`ContainerSupport#guarded_mutation`). Field and array stores publish only a symbolic value or into
an already-tracked location (`BI` putfield/array-store paths), so the guarded clause of
`publish_value` never starts a scalar log.

### 5.4 Observation

`observeExactPrimitiveField(owner, fieldSignature)` (`VM/concolic/concolicMngr.cpp`) accepts a
non-static field of type `boolean`, `byte`, `char`, `short`, `int` or `long` (anything else prints a
warning and does nothing). Unless the location is tracked, it installs the current value as a
concrete expression and publishes an INITIAL version with it, so the next concrete store is a
`WRITE` and the next read names a version. SYMBOL-SCOPE.md §5.2 says where it is woven.

### 5.5 Bounds and threads

At most 64 versions per location (dropping the oldest clears `writerSetComplete`) and 1024 reads
(dropping sets `readLogTruncated`). Locations are never evicted before session close. A thread
outside every region has no `ThreadContext`: its scalar stores to tracked locations are versioned
without writer, guard or site; its reference stores are dropped (§8).

## 6. Containers

A container's state is an immutable `ContainerExpression` chain (`base + PUT/REMOVE/...`) on
`STATE(identity)`, keyed by the container's `_sym_rid`; views and iterators alias their owner. A
log opens with an INITIAL version stating what the container held when tracking began
(`ContainerSupport#snapshot_for_receiver`): walkable for the modeled classes and `Object[]`, capped
at 64 members, else a stated refusal (`NO_MODELLED_SHAPE`, `UNREADABLE_CONTAINER`,
`MUTATED_BEFORE_FIRST_READ`). `compose/ContainerStateModel` and `compose/ContainerSmtCodec` lower
the chains (`AssocState` for maps, `IndexedState` for lists and arrays).

**Array reads over recorded writes.** The writes at concrete positions of one array chain share
one index of what was stored where (`ElementWrites`, `ContainerExpression::stored_at`: one lookup,
no walk of the chain). An array load at a concrete position is answered from it
(`ContainerSupport#recorded_element`): the value the newest write at that position stored, or,
for an element no recorded write replaced, the heap's own value as a concrete; no READ node, no
index and no condition. The load stays a READ below a write at a symbolic position, on a forked
chain or a consumer-boundary receiver, at a symbolic position, and for an array whose elements are
an input (one a symbolization reached, or whose shadow stands for a semantic value). The array's
identity node is built only when it roots a new state.

## 7. Wire handoff

`VM/concolic/expressionBroker.{hpp,cpp}`: `exportExpression` publishes the live expression of an
instance field and returns an opaque handle `(epoch << 32) | serial`; `attachExpression` resolves a
handle and installs the expression as a `ConsumerBoundaryExpression` on the destination field (a
container leaf becomes the destination container's state). Handles live for the session: any
region on any attached thread of that session can attach; a handle of another session is
`FOREIGN`. Statuses: `NO_ACTIVE_REGION -1`, `MISSING_METADATA -2`, `FIELD_NOT_FOUND -3`,
`NOT_SYMBOLIC -4`, `FOREIGN_HANDLE -5`, `UNKNOWN_HANDLE -6`, `SORT_MISMATCH -9`,
`UNSUPPORTED_TARGET -12`. The handoff is same-JVM: bytes cross between nodes concretely, and the
handle rides the message envelope (SYMBOL-SCOPE.md §6.3).

## 8. What the VM publishes

`jdk/src/share/classes/java/lang/System.java` declares 32 concolic natives (registered in
`jdk/src/share/native/java/lang/System.c`, implemented in `VM/prims/jvm.cpp`).
`runtime/ConcolicVmBroker` looks 23 of them up by reflection, so it loads on a stock JDK, and
`#requireCurrentCapabilities` refuses a replay plan before its workload starts when any is missing:
sessions, regions, context and event ids, `symbolize`/`symbolizeField`/`symbolizeExactField`,
`observeExactPrimitiveField`, `getSymbolicExpression`/`getSymbolicFieldExpression`, path-condition
pause/resume, branch events and range, `endConcolic`, `exportExpression`/`attachExpression`,
`getTrackedLocationVersions`, `installGuardedStoreSites`. `markConcolicBranch` and the pause
natives are called by woven code (`CausynthPipeline.HookCatalog#concolic`). The broker mirrors the
statuses `OK 0`, `MISSING_METADATA -2`, `NOT_SYMBOLIC -4`, and its own `INVOCATION_FAILED -1001`,
`MALFORMED_RESULT -1002`, and names every status in the gap a refused export or attach files
(`ConcolicVmBroker#statusName`).

- Expressions are published as a DAG envelope (`VM/concolic/exp/expression.cpp`, iterative
  serializer); the engine keeps them in each session's `expressions.jsonl` (CONTRACT-SPEC.md).
- `getTrackedLocationVersions(afterEventId, maxBytes)` pages the version and read logs by the
  session clock (`SFV`).
- Natives no engine code calls: `getPathCondition`, `trackContainerExpression`,
  `armSharedPrimitiveFieldRead`, `confirmSharedPrimitiveFieldRead`, `getSharedFieldVersions`,
  `getSharedElementVersions`, `getSharedMapVersions`, `getConcolicRegionSummary` (only the smoke
  tests use them).

## 9. Value movement

How a value's expression survives each way it can move. **Hooked**: a VM hook moves the shadow.
**Modeled**: an API model keeps the relation. **Detected and pinned**: the loss is named (an
`UNOBSERVED` version, a return symbol stating its concrete value, a named operation, or
`writerSetComplete = false`). **Silently lost**: the relation is dropped with no trace; *wrong*
marks the worse case where a stale or foreign expression stays and the solver is handed a relation
that does not hold.

| movement | class |
|---|---|
| interpreted bytecode, application or library callee | hooked |
| thread handoff (field, queue, `Future`, `ThreadLocal`) to a reader inside a region | hooked; versioned if tracked |
| `Method.invoke`, `Constructor.newInstance` | hooked |
| byte encode/decode inside one heap array (`i2b`, shifts, `DataOutputStream.writeInt`, heap `ByteBuffer.putLong`) | hooked (INDEXED chains) |
| `Unsafe.get<Primitive>(Object, long)` | hooked (field shadow, bypassing the version log) |
| `String` and `StringBuilder.append`, boxing, `HashMap`/`ArrayList`/... operations, atomic RMW | modeled (§4) |
| `Integer.parseInt`, `Long.parseLong` | detected and pinned (return symbol with its concrete value) |
| primitive-to-string conversions other than `Integer.toString` | detected (a named operation, not pinned) |
| a tracked scalar changed by a write the hooks never saw | detected and pinned (`UNOBSERVED`) |
| map `putIfAbsent`/`putAll`/`replace*`/`compute*`/`merge`, list `removeIf` on a tracked container | detected (`writerSetComplete = false`); on an untracked one silently lost |
| `System.arraycopy`, `Arrays.copyOf`, stream `write(byte[])`/`readFully`, `ByteArrayOutputStream` | silently lost; wrong where the destination already has an INDEXED chain |
| `Object.clone` and array `clone()` | silently wrong: `JVM_Clone` copies `_sym_rid`, so the clone shares the original's shadow, container state and version log |
| `valueOf` returning a cached box (`Integer`/`Short`/`Long`/`Byte` in -128..127, `Character` <= 127, `Boolean.TRUE/FALSE`), and a container result that is a shared object | silently wrong: the expression is set on the JVM-wide shared object |
| `Unsafe` puts, volatile or object gets, CAS and `getAndX` (`ConcurrentHashMap` slots, atomic `lazySet`/`getAndSet`, `AtomicBoolean`/`AtomicReference`, field updaters, reflective `Field.set`) | silently lost, or wrong (the old field shadow stays); detected only at a later in-region read of a tracked scalar |
| a native method with a symbolic argument (JNI, most JDK natives) | silently lost |
| `String.toCharArray`/`getBytes`/`getChars`, `new String(bytes)` | silently lost |
| `StringBuilder.insert`/`delete`/`replace`/`reverse`/`setCharAt`/`setLength` | silently wrong (stale builder expression) |
| `StringBuilder.append(Object)` of an unshadowed non-String | silently wrong (appends `""`) |
| operations of an unmodeled collection | element fields hooked; the container relation silently lost |
| digests, MACs, ciphers, logging | silently lost by design (muted) |
| Jackson generator and bean writer, direct `ByteBuffer` | silently lost (muted or `Unsafe`) |
| a value handed to a thread outside every region | silently lost; its scalar writes to tracked locations are versioned unattributed, its reference writes dropped |
| a separate process | silently lost (no mechanism) |
| clocks, `Random`, `identityHashCode` | concrete natives; clocks become roots only through the Java-side mint |

## 10. Current limits

- Silent losses and silently wrong relations, as listed in §9.
- Decisions never recorded: `instanceof`; implicit-check exceptions (a null dereference of a
  symbolic reference, an out-of-bounds index, division by zero, a failed cast) are never branch
  outcomes; `multianewarray` dimensions; branches before a region's admission gate; symbolic
  branches the weave did not mark (they enter only the thread-wide condition, which the engine
  never reads). A version's guard holds only the innermost region's decisions.
- Re-pairable state is integral fields, modeled containers and the two atomics. A container
  reached through a replaced reference field carries no state (the state follows the object, not
  the field); a guarded concrete store to a scalar field or array element starts no log (§5.3).
- A reference stored by a thread outside every region publishes nothing, so readers keep resolving
  to the stale referent with `writerSetComplete` still true.
- A container attach sets the destination's state but publishes no `MAP_STATE` version.
- An INITIAL snapshot that is a refusal is serialized with `stated: true`.
- `getTrackedLocationVersions` paging selects locations by their highest event but resumes at the
  lowest event of the first unemitted one, so above the byte budget pages repeat and the resume id
  can go backwards.
- A reader that loads a new word before its writer publishes records a spurious `UNOBSERVED`.
- `symbolize` stops at depth 5; mint failures print to the console only; a null argument to a mint
  native aborts through `guarantee`. Symbol names are truncated at 1024 bytes; some model paths
  abort on unexpected shapes (`symbolicString.cpp`, `symbolicStringBuilder.cpp`,
  `symbolicBigDecimal.cpp`).
- Cost: every expression lives until session close under one global arena mutex; every in-region
  field access takes the heap lock; a tracked read takes the version lock twice; the path-condition
  byte bound (`-Dcausynth.vm.pathcondition.bytes`) counts reference bytes only.
- The armed-read override (`armSharedPrimitiveFieldRead`) is still consulted in the `getfield`
  path though no engine code arms it.

## 11. Smoke tests

`third_party/OpenJDK-Concolic-Execution-Engine/scripts/causynth_smoke_test.sh` compiles the 47
`test/causynth/Region*Smoke.java` files and an slf4j probe, and runs each under `-Xint` with
`JDK_HOME` set to the image; `RegionPathConditionTruncationSmoke` runs again with the byte bound
unset, 0 and 8192. A test fails by throwing. The script is run by hand; neither `mvn test` nor
`run_engine.sh` runs it. No smoke test covers the collections the VM does not model,
`AtomicBoolean`/`AtomicReference`, `System.arraycopy`, `clone`, a cached box, reflective
`Field.get/set`, or anything across JVMs.
