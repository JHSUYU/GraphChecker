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
- Class redefinition (a JVMTI agent's retransform: mockito-inline retransforms every superclass of
  a mocked type, `java.lang.Object` included): a Zero interpreter frame has no pc and no code blob,
  so `frame::metadata_do` (`VM/runtime/frame.cpp`) asks the frame itself whether it is interpreted,
  and `MetadataOnStackMark` marks the method it runs. A redefined method still running in some
  frame (a thread parked in the old `Object.wait`) is kept as a previous version until it returns,
  and a class-unloading GC frees only what no stack runs. A GC that frees metadata (those old
  versions, an unloaded loader's classes) drops every cache keyed by a `Method*` or `Klass*`
  address, which the VM reuses: the guarded-store memo (§5.3) and the container field offsets
  (`ConcolicMngr::metadata_freed`, called from `VM/classfile/classLoaderData.cpp`).

## 2. Shadows, sessions, regions

- **Object identity.** Every object carries an extra header word `_sym_rid` (`VM/oops/oop.hpp`);
  it survives GC and is reset at every allocation path and on an `Object.clone` copy. Heap shadows
  (`SymInstance`, `SymArr`, container states) live in the session heap keyed by it
  (`VM/concolic/sessionSymbolicHeap.cpp`). An interned String's header is never written: an
  identity the session gives it lives beside it (a detached entry), and it carries no expression.
  One rule: a JVM-wide identity (an interned String, a JDK box-cache entry or a cache's own array,
  `Boolean.TRUE/FALSE`, an enum constant; `symbolicPrimitive.cpp#jvm_shared_object`) never carries
  an expression. A value it stands for rides the slot that holds it. Every mint asks first: the
  boxing and container models, `mintLeaf` (§7), and the symbolizers (`VM/concolic/fieldTraverser.cpp`,
  `threadContext.cpp#symbolize_*`). A JVM-wide root or owner is not minted and the region's gate
  stays as it was (a symbolizer opens it only once it mints); a walk does not enter a JVM-wide
  object; a field holding a box, shared or fresh, is minted on the field as a value of the box's
  sort (what an unboxing of it reads, under the primitive fields' replace rule) and the box stays
  clean; a String field is minted on the field; any other JVM-wide referent (an enum constant) of
  a selected field binds the field to a reference symbol, as a null one does.
  `getSymbolicExpression` states `jvmShared` for an object, so a caller names a refused mint by
  what it is.
- **Stack shadows.** One `ThreadContext` per thread (`__thread`, `VM/concolic/concolicMngr.cpp`)
  shadows operand slots and locals; arguments and returns move through `ShadowStack` at every Zero
  frame push and pop (`VM/concolic/shadow/shadowStack.cpp`).
- **Session.** `openWorkloadSession` / `closeWorkloadSession`: one per workload JVM. Every
  expression is allocated in one session arena (`VM/concolic/globalSymbolicSession.cpp`) and freed
  at close; one event clock numbers versions, reads and region entries (`currentSymbolicEventId`).
- **Regions.** `startConcolicRegion` / `finishConcolicRegion` bracket one activation on one thread;
  each region frame owns its guard and branch events (`VM/concolic/threadContext.cpp`); the path
  holds a marked branch's conditions and nothing else -- a model states what it chose and what it
  observed on the nodes it builds (§6, the pin/guard discipline). Nothing is recorded in a region until it reads something
  symbolic (the admission gate); `observeField`, every mint, a getfield that yields an expression,
  and a modeled call whose value operand (a String, a box or a StringBuilder) carries its own
  expression (one a decode minted, `MethodSymbolizerHandle::general_check_param_symbolized`) open
  it. An owner whose field was symbolized is marked the same way, but passing it along (a
  `map.put(k, owner)`) opens nothing, and nothing opens it while observation is paused.
- **Branches.** The weave marks decision sites with `markConcolicBranch(siteId, ...)`; a marked
  branch is an event even when concrete (zero conditions). `getConcolicBranchEvents` returns the
  events since the last read; `getConcolicPathConditionRange` a range of the region's conditions.
  `pauseConcolicPathCondition` / `resumeConcolicPathCondition` (nestable) mute recording around the
  engine's own code: every hook call the weave emits, and the engine code the JDK runs on a
  program thread (an inheritable thread-local's `childValue` in `Thread.init`,
  `runtime/InheritedState`). Paused, the interpreter propagates nothing and no model runs
  (`ConcolicMngr::can_do_concolic`), so the engine's lists over program objects shadow none of
  them.

## 3. Propagation through bytecode

| bytecodes | behaviour |
|---|---|
| constants, `new` | push no expression |
| loads, stores, `iinc`, stack ops | move the shadow |
| int/long/float/double arithmetic, `neg`, shifts; the 15 conversions (`TypeCastExpression`) | build the expression; `iand`/`ior`/`ixor` over booleans become `&&`, `\|\|`, `!=` |
| `lcmp`, `fcmp*`, `dcmp*`, `if*`, `if_icmp*`, `if_acmp*`, `ifnull`/`ifnonnull` | branch conditions |
| `tableswitch`, `lookupswitch` | the taken case; the default arm is the conjunction of `sel != k` over every key |
| array loads/stores, `arraylength`, `newarray`/`anewarray` with a symbolic length | INDEXED read/write over the array's container state; a symbolic index records `idx >= 0 && idx < SIZE`; a load at a concrete position the recorded writes decide builds no READ (§6); the first symbolic store into an array starts its element's log |
| `getfield`/`getstatic` | the field shadow, resolved through the version log where tracked (§5); a demand-minted `FieldAccessExpression` where the owner is shadowed; a box's `value` read from a box that carries no expression is the box slot's expression (the unboxing of a slot-carried value) |
| `putfield`/`putstatic` | set the field shadow; publish a version (§5); a reference is symbolic only by what it carries (§5.1) |
| `invoke*` | argument and return transfer; model dispatch (§4) |
| `Method.invoke`, `Constructor.newInstance` | boxed arguments and result carried (`VM/runtime/reflection.cpp`) |
| `checkcast`, `monitorenter`/`exit` | concrete |
| `instanceof` | concretized: no condition |
| `multianewarray` | dimension expressions dropped |
| exception unwind | shadows cleared |

## 4. Calls and library models

`VM/concolic/methodSymbolizer.cpp` intercepts a call when the callee's holder class name equals a
registered model, a boxing class, or a muted prefix. A container model then decides by the
receiver's concrete class (`ContainerSupport::capability`), not by the holder: an application
subclass of a modeled class reaching a modeled holder is refused by name
(`CONTAINER_SUBCLASS_UNMODELED:<class>`, as is a LinkedHashMap in access order,
`ACCESS_ORDER_UNMODELED`) and runs as bytecode. Any other Java callee is interpreted and
propagates normally. A native with a
symbolic argument returns a concrete value, except `Unsafe.get<Primitive>(Object, long)`, which
returns the field shadow at that offset (`VM/concolic/native/nativeGetPrimitiveHandler.cpp`). A
model never reads a native's primitive result: it is still in `native_entry`'s C local when the
frame pops (`MethodSymbolizerHandle::result_readable`).

**Unsafe writes** (`VM/concolic/unsafeAccess.{hpp,cpp}`, hooked in `VM/prims/unsafe.cpp`):
`put*`, `put*Volatile`, `putOrdered*` and `compareAndSwap*` on a location of a shadowed object are
versioned in the native, in one critical section with the concrete operation. The value is the
caller's operand shadow, captured by the Unsafe model at the call boundary (`put*`,
`compareAndSwap*`, `getAndAdd*`, `getAndSet*` called from ordinary code), or the atomic model's
intent; a write from a thread outside every region is unattributed; any other write (a muted
subtree's) is versioned with its concrete word and marks the location
`UNSAFE_WRITE_UNCAPTURED`. A write to a shadowed object also updates its field shadow or the
array's state. A captured compare-and-swap that compared something symbolic (a tracked location's
read, or a symbolic expected value) records `old == expected`, or `!=` when it failed, as a path
condition; a capture is cleared by the write it was taken for.

**Callback window** (`MethodSymbolizer::enter_callback`/`exit_callback`, hooked in
`JavaThread::push_zero_frame`/`pop_zero_frame`). A modeled call's functional arguments (parameters
typed `java/util/function/*` or `java/util/Comparator`) are named at its invoke. While its body runs
muted, a frame whose receiver is one of them is a callback: it runs with propagation in a shadow
frame of its own (`ShadowStack::push_callback`), its parameters seeded by the model's contract
(`CallbackSeeder`, told which functional object is called back), and the muted call's handle is
suspended on a stack (at most 4 deep), so a
model call inside the callback nests. When its frame pops, what it returned (its expression, else
its concrete value) and the conditions its path recorded (`path`, `path_negation`: a predicate
compiled to branches returns a constant) are logged on the call (`CallbackResult`; a predicate's
answer as a condition is `CallbackResult::truth`), and the model's finish builds the mutation from
the log. A model may instead read each callback as it returns (`CallbackListener`: its result, the
object it returned, its arguments as its frame then holds them); a concrete result is then not built
into an expression, so a call whose callbacks stay concrete allocates nothing per callback (the stream
model). A model may name the container its call reads as its callbacks run (`MethodSymbolizerHandle::
set_source`, a stream's source): a mutation of it by a callback marks the call reentered without
refusing the mutation (`MethodSymbolizer::reenters`, asked by all three container models before a
mutation, `ContainerSupport::reenters_from_callback`), and the call's model states the rest. Any
application method -- a class no boot loader defined -- that a muted call with callbacks enters other
than as a callback (an element's `compareTo`, `equals` or `hashCode`, a custom list's `get`) ran
unhooked: the first one is named in the region's model gaps as `MUTED_APPLICATION_CODE:<class.method>`
unless the call's model states it itself. A call that unwinds with an exception tells its model
(`CallUnwound`). Its side effects are hooked like any interpreted
code. A callback the stack declines (a fifth window) runs muted and unlogged, and its call refuses
its map (`CALLBACK_DEPTH_EXCEEDED`). A callback that calls back into its call's map is refused
(`CALLBACK_REENTERS_CONTAINER`). A call that mutates as its callbacks answer (`removeIf`,
`replaceAll`) and unwinds with an exception after one ran refuses its map
(`CALLBACK_THREW_AFTER_MUTATION`). An unmarked JDK branch inside a callback (`maxBy`) chooses a
value the result then pins by identity.

**Muted subtrees** run concretely and return no expression: `org/slf4j/`, `org/apache/log4j/`,
`org/apache/commons/logging/`, `java/util/logging/` (observation only), `com/sun/crypto/provider/`,
`sun/security/provider/` (one-way functions), `sun/misc/Unsafe`, `sun/instrument/TransformerManager`,
Jackson's `UTF8JsonGenerator` and `BeanPropertyWriter` (`VM/concolic/reference/symbolicMiscObjects.cpp`).

**Models** (`VM/concolic/reference/`):

| class | modeled | not modeled |
|---|---|---|
| `String` (entered only with a symbolic operand) | `charAt compareTo concat contains endsWith equals equalsIgnoreCase hashCode indexOf isEmpty lastIndexOf length matches regionMatches replace* split startsWith substring toLowerCase toUpperCase trim valueOf ...`; results are string operations | `toCharArray`, `getBytes`, `getChars`, `new String(bytes/chars)` return no expression |
| `StringBuilder` (and its `AbstractStringBuilder` methods) | `append` (as concat; `append(CharSequence, start, end)` of a String or builder as a concat with its `substring` of `[start, end)`, of a `char[]` or another `CharSequence` with no expression of its own as a concat with the text it appended, of one with an expression as a concat with a named `unsupportedCharArrayRange`/`unsupportedCharSequenceRange` over it), `toString`, `length`; `insert delete deleteCharAt replace setCharAt setLength` as a concat of substrings of the content (an operand's slot shadow first) | `reverse`, `appendCodePoint` and a padding `setLength` drop the expression (the next use states the concrete content); `StringBuffer` |
| boxing `valueOf`, `new X(v)` for `Boolean Byte Character Short Integer Long` | the value on the result slot, and on the returned object unless it is JVM-wide | `Float`/`Double.valueOf`. This JDK's `Integer/Long/Short/Byte/Boolean.valueOf` box afresh; `Character.valueOf` caches 0..127 |
| decimal and boolean renderings: `Byte/Short/Integer/Long/Boolean.toString` (static of the class's own primitive, and the instance form), `String.valueOf` of an `int`, `long` or `boolean` or of such a box | one `toString` op of the value (`StringBuilder.append` wraps every primitive in the same op) | radix and hexadecimal conversions and char or floating renderings become a named `unsupportedPrimitiveStringConversion:` operation; `String.valueOf` of a char, float, double or other object stays a `valueOf` op |
| `Integer.parseInt`, `Long.parseLong` | a method-return symbol stating its concrete value and its call (holder, name, descriptor, argument expressions) | |
| `BigDecimal` | 8 signatures | `<init>(double)`, `<init>(String)` mint symbols unrelated to the argument; `BigInteger` |
| `AtomicInteger`, `AtomicLong` | `getAndIncrement getAndDecrement incrementAndGet decrementAndGet getAndAdd addAndGet compareAndSet weakCompareAndSet`, when the receiver is shadowed: the model states `new = old op delta` (or the CAS's expect/update) as an intent, and the compare-and-swap that performs it reads `old` at the word it compared and publishes the RMW version, in one critical section; a failed CAS reads the word it lost to | `set` is a putfield; `lazySet`, `getAndSet`, `AtomicReference`/`AtomicBoolean` (`value` observed on the atomic; `get`/`set` are a getfield/putfield, a CAS answers `old == expected` over the value it compared as its result), field updaters are versioned as Unsafe writes with their captured operands, not modeled; `accumulate*`, `LongAdder`, atomic arrays |
| maps by the Map contract: `HashMap`, `LinkedHashMap` (insertion order), `ConcurrentHashMap`, `Hashtable` (views, iterators, entries, a map view's `Collection.removeIf`) | `put get getOrDefault remove containsKey isEmpty clear size mappingCount entrySet keySet values iterator hasNext next getKey getValue`, conditional removal; `putAll` (a tracked source as `PUT_ALL` of its state read, else one `PUT` per entry); `putIfAbsent`, `replace`, `remove(k, v)`: `PUT_IF`/`REMOVE_IF` under the test the body made (§6); `computeIfAbsent computeIfPresent merge`: the callback's result stored under the test that ran it, what a callback that did not run would have stored an unknown cell; `compute`: the callback's result stored (`PUT`, or `REMOVE` for null); `replaceAll`, `forEach`; key and entry views' `removeIf` (`REMOVE_IF` under the predicate) | `Entry.setValue` abandons the entry; `values().removeIf` (`ASSOCIATIVE_VALUES_REMOVE_IF_UNMODELED`); `ConcurrentHashMap`'s bulk parallel operations |
| `ArrayList`, `ArrayDeque`, `AbstractList` iterators | list and deque operations; `peek`/`poll` as `PEEK`/`POLL` (§6) | `removeIf` abandons |
| `HashSet`, `LinkedHashSet`, `ConcurrentHashMap`'s `KeySetView` (its map's location) | set operations | a hash set's reads are not bound to versions |
| `java.util.stream` sequential pipelines from `Collection.stream()` of a modeled container (a list, a deque, a hash set, a key/entry/values view, an unmodifiable map's entry set) | `filter map limit sorted distinct unordered`; `collect(Collectors.toList()/toSet())`, `toArray`, `count`, `anyMatch allMatch noneMatch` stated as relations; `findFirst findAny forEach forEachOrdered` run on the run's values (below) | `skip peek flatMap* mapTo* reduce min max iterator spliterator parallel`, `collect` with any other collector, `parallelStream()`, and every pipeline over another source (`Arrays.stream`, `Stream.of`, `IntStream`) run as bytecode |
| commons-lang 2 and Spring `StringUtils` | `isNotBlank`, `isEmpty` | commons-lang3 |

Every other collection (`TreeMap`, `TreeSet`, `ConcurrentSkipList*`, `LinkedList`, `CopyOnWrite*`,
`PriorityQueue`, blocking queues, `IdentityHashMap`, `WeakHashMap`, `EnumMap`) is interpreted as
plain objects: its elements' fields propagate, but it has no container state and no version log.
A modeled call with a callback on one of the four maps is admitted when an argument is symbolic or
the map's state is tracked; otherwise it runs as bytecode. A visiting callback (`forEach`,
`replaceAll`, `removeIf`) is seeded with a READ of the state per element, so a decision on it is
one path condition per element per call; past the snapshot bound (64,
`-Dcausynth.concolic.initial.snapshot.max`) a call's visits are not seeded and it refuses its map
(`CALLBACK_VISITS_OVER_BOUND`).

**Streams** (`VM/concolic/reference/symbolicStream.cpp`, `SymStream`). `Collection.stream()` of a
modeled container (`ContainerSupport::backing_container`; SymMap holds `java/util/Collection` and
routes it) records the pipeline on the stream object it returns -- bookkeeping in the thread's
`StreamTable`, never an expression: the source (a weak global handle) and its view
(`SymMap::view_kind`). Each modeled intermediate call keeps one stage on the stream it returns; every
body runs muted. Streams bind late: the terminal reads the source's state
(`ContainerSupport::observed_state`), member count (`ContainerSupport::member_count`) and, for a
values view of a stateful map, the keys its iteration holds the values under, and names the source
as the call's (a callback mutating it unstates the result, `CALLBACK_MUTATES_SOURCE`). The terminal
call runs muted with every stage's functional object a callback: an element's first callback is
seeded with the source's member (a `READ` of the list's state at its position, a map view's
`ENTRY`/key by `SymMap::visited_member`, a value's `READ` at its key, the keyed ones where the state
`CONTAINS` the key), each later one with the previous map's result, and the elements'
progress is reconstructed from the answers as each callback returns (a sequential pipeline calls
the stages per element in order and stops an element at the first filter that answers false; a
`LIMIT` lets an element through while fewer than maxSize passed before it in that world, `SIZE` of
the earlier arrivals' guarded chain). An element of the run's own value is named only where a
statement needs it: a collected list's members are read back from the list, a set's members and an
element a symbolic filter dropped are named by the object their callback returned or still holds
when it returns (else that drop is pinned) -- so a pipeline that stays concrete allocates no
expression. The terminal states its result: a collected list is an `INDEXED` chain from its stated empty
base, one `APPEND_IF` per element under its filters' answers and limit positions, published as its
first version (`ContainerSupport::publish_filled`, `STATE_COLLECT`); a set the same with `PUT_IF`;
`toArray` the chain as the array's state; `count` the chain's `SIZE`; a match the `IS_EMPTY` of the
chain of its matches (misses for `allMatch`). What the run decided and nothing states is a `PIN` on
the chain, in the run's polarity: an element a symbolic filter dropped before a stage that calls back
(`DROPPED`), the members an exhausted limit or a short-circuiting match never pulled
(`LIMIT_EXHAUSTED`, `SHORT_CIRCUIT`), a stateful source holding exactly what the stream pulled
(`SOURCE_END`: its `SIZE` equals the positions pulled, or the `SIZE` of the chain of the pulled keys
it `CONTAINS`), a symbolic maxSize's sign. A result no relation states -- a symbolic element entering
`sorted` or `distinct` (members of a stateful source, or past a symbolic bound, entering one ahead
of every callback count), a symbolic comparator, a natural order an application `compareTo`
decided, more members than the snapshot bound, callbacks the reconstruction contradicts (an element
left waiting for a callback included), a collected list whose members are not the run's, a callback
mutating the source, `findFirst`/`findAny` -- is the run's own concrete value; `forEach`'s action
runs seeded, its effects hooked, and each pin, which no chain holds, is only named. Each is named in
the region's model gaps (`ThreadContext::note_model_gap`, §8) as `STREAM_PINNED:<reason>`, as are a
mapped value or an answer a callback's path decided (`MAP_PATH`, `CALLBACK_PATH`, not pinned: the
path holds models' concrete-answer conditions too), application code the body ran unhooked
(`MUTED_APPLICATION:<class.method>`) and a terminal that unwound (`UNWOUND`); an unmodeled call ends
the recording and the rest runs as bytecode, named `STREAM_OPERATION_UNMODELED:<operation>` when the
source's state or a symbolic bound was in it; and a terminal past the callback window stack runs as
bytecode, `STREAM_PINNED:CALLBACK_DEPTH`. A pipeline nothing symbolic reached returns the run's
result and names nothing. `Collectors.toList`/`toSet` are muted to name the kind of collector by its
accumulator, the one non-capturing method reference every such collector holds, so a collector kept
in a field is known at every use.

## 5. Shared-state versioning

`SFV` keeps a version log per location `(ownerSymRid, slot, kind)`, kind `INSTANCE_FIELD`,
`STATIC_FIELD` (owner = the class mirror), `ARRAY_ELEMENT`, or `MAP_STATE` (a container's whole
state, slot `-3`; a view and its map are one location). Version kinds: `INITIAL`, `WRITE`, `RMW`,
`STATE`, `UNOBSERVED`. A version carries its expression, writer, site, path guard and the concrete
word the store left: a scalar's bits, a reference's referent session id (named on demand; null is
0), a wrapper-typed field's box primitive or the null word. A container state has no word.

**One critical section per tracked access.** A tracked scalar store is the concrete store, its
version id and its append under the location's lock (one of 64 stripes); a tracked load is the
concrete load, the comparison with the newest version and the read record under it
(`SFV::begin_store_locked`/`end_store_locked`, `plan_read_locked`; `BI` getfield/putfield and array
paths, `unsafeAccess`). Log order is heap order, so a mismatch can only mean a writer no hook saw.
Container versions carry no word: a container mutation is a Java call no lock can span.

### 5.1 When a location is tracked

Tracking is by value; nothing is declared in advance. A log starts at the first symbolic store
(field or array element), a mint, an attach, a symbolic container operation, an admitted guarded
store (§5.3), or `observeField` (§5.4). A log a symbolic store starts has no INITIAL: the value
that store wrote is the first thing it knows, and a store before it is no version
(`SFV::begin_store_locked`). Once tracked, every store to it is versioned,
concrete ones included, with the stored operand, not a heap re-read. A mint, an attach and an
observation read the word they state under the location's lock (`publish_held`,
`publish_initial_held`).

A stored reference is symbolic by what it carries: its slot's expression, else the expression its
object holds as its own (`ContainerSupport::semantic_value`: a decode's mint, a model's result).
Null, and a shadow that only names its object (an owner of a tracked field, a referent named
once), are concrete (`putfield`/`putstatic`, `aastore`), as a model's argument is
(`MethodSymbolizerHandle::general_check_param_symbolized`): naming an object is not making it
symbolic. Counted symbolic, a name started a log at every location it was stored into, gave each
owner a shadow in turn, and a load of it from such an array made the element demand-symbolic,
every field read of it a projection; in hdfs-17960 the image's name reached the checkpoint
savers' threads, and their context class loader 13k rows of a configuration parse. A concrete
reference stored where a log stands is versioned as any concrete store is, naming its referent.

### 5.2 Reads

A read of a tracked location resolves to the newest retained version and states the word it
loaded. When that version stored another word, a write the hooks never saw came between (a muted
subtree's store, JNI): the read names a retained version that stored exactly the loaded word if
there is one (ABA: a newer hooked version overwrote it, so the read is not exact), else publishes an
`UNOBSERVED` version holding the loaded constant (a reference: the loaded referent), minted under
the lock; either way the location is marked incomplete (`UNOBSERVED_WRITE`). Every read states
`observedExact` (the loaded word equals its observed version's stored word and that version is the
newest; never for a container read), `writerSetComplete` (the location's writer set as of the read)
and, when true, `unnamedWriter` (a writer the log never named reached the location: every
incompleteness reason but `VERSION_BOUND`); a read that returned its version's word shares that
version's constant, or for a reference its identity node. The location's read log keeps the same
answer per read (`ReadRecord`: `readEventId`, the reader, its `site`, `observedVersion` -- the
chosen version's id --, `observedExact`, `writerSetComplete`, `unnamedWriter` when true, and
`_java_type`, the loaded word's letter, absent for a container's state), so a read whose value
reaches no published expression (a reference compared with a constant) is still a read of its
version (SYMBOL-SCOPE §5.2).

### 5.3 Guarded concrete stores

The session's guarded-store table (`installGuardedStoreSites`, from `runtime/GuardedStoreSites`)
lists the scope map's control-dependent store sites but stores into a field only its class's
construction stores (SYMBOL-SCOPE §5.1, `constructionOnly`), one line each: the method, the store (`FIELD
a/b/C.f`, or `CALL <name>` for a container mutation), and the site's guard branch sites. A concrete
store at a listed site, after one of that site's guards decided symbolically on this path, starts the
location's log: a container mutation (`put`, `remove`, `clear`, `add`, `offer`, `set`;
`ContainerSupport#guarded_mutation`) publishes a `STATE` version over its stated base; a
`putfield`/`putstatic` publishes an `INITIAL` of the word it replaced, then its `WRITE` (the owner
is given a shadow if it has none). Neither states a path guard. Another store in the same method is
not admitted; nor is an array-element store (the scope map lists none). A method's rows are looked
up once per thread per table (a thread-local memo keyed by the `Method*`), so the map lock is taken
once per method, not per store; a GC that frees methods discards every memo (§1).

### 5.4 Observation

`observeField(owner, declaringClass, fieldName, descriptor)` (`VM/concolic/concolicMngr.cpp`)
accepts a field of type `boolean`, `byte`, `char`, `short`, `int` or `long`, of the wrappers
`Boolean`, `Byte`, `Character`, `Short`, `Integer`, `Long`, or of any reference type; `owner` is
the object, or the declaring class's `Class` for a static field (keyed by its mirror, as
`getstatic` keys it). Unless the location is tracked, it installs the current value (a wrapper
field: its box's constant, or null; a reference: the referent's identity) as a concrete expression
and publishes an INITIAL version with it and its word, so the next concrete store is a `WRITE` and
the next read names a version. No referent is snapshotted there. It answers a status:
`0`, or `-1` (no context), `-2` (an argument missing), `-3` (no such field of that kind on the
declaring class), `-12` (`float`/`double`). SYMBOL-SCOPE.md §5.2 says where it is woven. A read of
a wrapper field is its value's sort (`J` for a `Long`) and its unboxing reads the read.

### 5.5 A container behind a reference

A store of a reference into a tracked cell (putfield/putstatic, aastore, an Unsafe put or CAS:
`AtomicReference.set`/`compareAndSet`/`getAndSet`/`lazySet`, reflection) states what the referent's
container state was, when the referent is a modeled container or a view or wrapper of one
(`ContainerSupport::backing_container`): `referentState {ownerSymRid, slot, locationKind:
MAP_STATE, fieldVersionId}`, the version of that container's location live at the store. It is
asked before the carrier's stripe (`SFV::prepare_referent`, `UnsafeAccess::begin`), never under
it; a container with no log starts one there with a stated snapshot. Otherwise the version states
`referentStateRefused`: `UNREADABLE_CONTAINER:<class>`, `TRUNCATED`, `RESIZING`, `NO_CONTEXT` (a
thread outside every region, and no log stands), or `STORE_NOT_PREPARED` (an arraycopy, or a
location that became tracked after the store asked). A read of a reference cell states the
identity it returned as its `concreteValue` (`ReturnedValue::REFERENCE`).

### 5.6 Bounds and threads

At most 64 versions per location and 1024 reads (dropping sets `readLogTruncated`). Locations are
never evicted before session close. A location's incompleteness reasons are published
(`incompleteReasons`: `VERSION_BOUND`, `UNOBSERVED_WRITE`, `UNSAFE_WRITE_UNCAPTURED`,
`UNHOOKED_ELEMENT_WRITE`, `UNNAMED_REFERENT`, `ARRAYCOPY_FAILED`, `ARRAYCOPY_STORE_CHECK`,
`ARRAYCOPY_RACE`, a container model's reason), with `unnamedWriter`: every reason but the version
bound is a writer the log never named, and removes a read's alternative writers at COMPOSE; the
bound only drops writers the log once named, so a hot field past 64 stores keeps its
alternatives. A thread outside every
region has no `ThreadContext`: its stores (bytecode, Unsafe, arraycopy) to tracked locations are
versioned without writer, guard or site, a reference by the referent it names.

## 6. Containers

A container's state is an immutable `ContainerExpression` chain (`base + PUT/REMOVE/...`) on
`STATE(identity)`, keyed by the container's `_sym_rid`. What is a container is the receiver's
concrete class (`ContainerSupport::capability`): the positional ones (arrays, `AbstractList`
subclasses, `ArrayDeque`), `HashMap`, `LinkedHashMap` (insertion order), `ConcurrentHashMap` and
`Hashtable` (null-free: present exactly when `READ != null`), the hash sets. Views, iterators,
entries and `Collections` wrappers (unmodifiable, synchronized, checked) are their backing
container (`ContainerSupport::backing_container`, through `this$0`, `map`, `m`, `c`): a view a
modeled call made is aliased to it, and one the program built resolves at `state_location` (a
`KeySetView` is aliased at its first model event). A log opens with an INITIAL version stating
what the container held when tracking began (`ContainerSupport#snapshot_for_receiver`): walkable
for the modeled classes and `Object[]`, each in the order its class's iterator returns them -- a
`LinkedHashMap` (and a `LinkedHashSet`'s map) from `head` by `after`, a `HashMap` and a
`ConcurrentHashMap` by their tables' bins from 0 up (tree bins by `next`, and by `first`), a
`Hashtable` by its bins from the last down; a `ConcurrentHashMap` resize in flight refused as
`RESIZING` (the log still starts, at the bare root), past 4096 bins over the bound -- capped at 64
members, else a stated refusal (`NO_MODELLED_SHAPE`, `UNREADABLE_CONTAINER`,
`MUTATED_BEFORE_FIRST_READ`). A map's or set's `SNAPSHOT_BASE` states the order those members
follow it in and how many of the `PUT`s above it they are (`order`: `INSERTION` or `HASH`,
`ContainerSupport::iteration_order`; `members`). `compose/ContainerStateModel` and
`compose/ContainerSmtCodec` lower the chains (`AssocState` for maps, `IndexedState` for lists and
arrays).

**An indexed size skips element sets.** Every INDEXED `SIZE` (`arraylength`, `List.size()`, the
stream models) is built over its state's size source (`ContainerExpression::size_source`, decided at
construction): an element set -- an INDEXED `WRITE` (an array store or `set()`: position and value)
-- never changes a size, so its size source is its receiver's; every other node is its own: `APPEND`,
`INSERT`, `REMOVE`, `POLL` and `CLEAR` change the size, and a consumer boundary or guarded read under
a chain is the container's provenance, never skipped. An array of constant length answers its length
concretely (`has_constant_size`). Built over the current state, hdfs-adhoc-03's packet `buf.length`
(a length that is no constant) carried every checksum byte written into the buffer, ten thousand
nodes more per chunk, to each branch on it (`RegionIndexedSizeSmoke`). `ContainerSupport::measures`
(`new T[c.size()]` filled by `toArray`) compares size sources.

**The owner of a relation.** A query or mutation whose receiver slot carried a guarded reference
read -- a tracked reference field, an `AtomicReference`, a container `READ` result -- states that
read as its `owner` member (`ContainerSupport::receiver_owner`), so the choice the read made
survives while the relation's receiver stays the observed object's state. A read of a reference
cell is its own owner even when the object it returned is a view (the view's node is not looked
through); relations built on a view, iterator or entry a container query returned inherit that
node's owner. Absent otherwise. A `Collections` wrapper held in a cell runs as bytecode and reaches
its map through its own untracked field, so a query through it carries no owner; the cell's
`referentState` then names a container that is not the stored object.

**Map operations beyond get/put.** `READ_OR_DEFAULT [k, d]` (`getOrDefault`), `PUT_ALL [source
state]`, `ENTRY [k]` -- the entry of key `k` a view's callback visits, whose `getKey`/`getValue`
answer `k` and `READ(state, k)` -- and `MATCHES [k, e]`: whether the value at `k`, null where `k` is
absent, is the cell `e` (the test the JDK's default Map methods make, `get(k) == null`,
`Objects.equals(get(k), e)`). A queue's `PEEK` is its head or null, and `POLL` the queue without its
head where it has one.

**The pin/guard discipline.** A model records no condition (a summary states no condition but a
marked branch's, `VM/concolic/threadContext.cpp`): what it decided and what it observed are
stated on the nodes it builds, and COMPOSE decides what holds (PIPELINE §8).

- A CHOICE a muted body made by the value at a key, a membership or an emptiness is the guard of
  the mutation it made, whichever arm the run took, so another state flips the effect:
  `putIfAbsent` is `PUT_IF` under `MATCHES [k, null]`, `replace(k, v)` under `CONTAINS [k]`,
  `replace(k, e, u)` and `remove(k, e)` `PUT_IF`/`REMOVE_IF` under `MATCHES [k, e]` (and `CONTAINS`
  for a null `e`); `computeIfAbsent` stores what its callback answered (`PUT_IF`) under `MATCHES
  [k, null]`, `computeIfPresent` (`PUT_IF`, or `REMOVE_IF` for null) and `merge` (the callback's
  result under the key's presence over the value under its absence) under its negation; a set's
  `add` is `PUT_IF` under the member's absence; `poll()` is `PEEK` and `POLL`, whose emptiness test
  is their own. What a callback that did not run -- `computeIfAbsent` over a present key,
  `computeIfPresent` and `merge` over an absent one -- would have stored is an `UNKNOWN` cell
  (`ContainerSupport::unknown_cell`, named by its `answer` id), put at its key under the arm it
  would have run in, named `CONTAINER_PINNED:<method>` in the region's `modelGaps`. A
  compute-family call answers `get(k)` as it left the map. `MATCHES` compares a String or a box by
  value, as `equals()` does, and any other object by identity; a match `equals()` found for an
  object whose class overrides it states no answer. A call that left the container as it was (a
  guarded mutation that did not fire: a hit, a miss, an unrun callback, a poll of an empty queue)
  is the thread's state (`set_container_state`) and no version, so it takes no slot of the
  location's log; a poll of an empty queue whose chain states no size
  (`ContainerSupport::stated_size`) states nothing.
- A FACT the run observed that the chain may not decide is stated on its node as `concreteValue`
  (`ReturnedValue`) with a session-unique `answer` id (`ContainerExpression::state_returned`):
  what a query answered (`get`, `getOrDefault`, `containsKey`, `size`, `isEmpty`, `hasNext`, a
  scalar iterator's `next`, an entry's key or value, a list's `get`/`set`/`remove`, a set's
  `contains`/`add`/`remove`, `peek`/`poll`), what the test of a choice found, and an element of an
  array whose elements are the heap's (a named shadow) at a position the chain does not decide
  (`ContainerSupport::element_read`; an array whose elements are an input states none: its `READ`
  is the input). A query bound to a version (`ContainerSupport::query_state`'s read-from) states
  none: a pin would choose its writer.
- A relation already on a node has no copy: a method-return symbol states its call; the codec
  requires a position or an entry a member; a captured compare-and-swap's `old == expected` is the
  result of the native it ran in (`UnsafeAccess::take_result`, read at that native's finish), which
  a branch on it decides; a field mint is its version and its shadow.

**Stream results** (§4). `APPEND_IF [v]` and `PUT_IF [k, v]` carry the `guard` they hold under;
`PIN` (no arguments, either shape) is its receiver's state where its `guard` holds. A version a
stream published is `STATE_COLLECT`; a map's guarded mutation is `STATE_PUT_IF`, a queue's poll
`STATE_POLL`. Of the VM's own chain readers, `ContainerSupport::position_answer` looks through a
`PIN` and replays a `POLL`, and `entry_answer` looks through a `PIN` and past a guarded mutation of
another key; across anything else they, `undo_indexed_history` and `snapshot_entry_count` decide
nothing: the member is a `READ`.

**Array reads over recorded writes.** The writes at concrete positions of one array chain share
one index of what was stored where, and what each left in the heap (`ElementWrites`,
`ContainerExpression::stored_at`: one lookup, no walk of the chain). An array load at a concrete
position is answered from it (`ContainerSupport#recorded_element`): the value the newest write at
that position stored, or, for an element no recorded write replaced, for a write that stored a
concrete value, or for one whose word the element no longer holds (a write no hook saw; the log is
marked `UNHOOKED_ELEMENT_WRITE`), the heap's own value as a concrete; no READ node, no index and no
condition. The load stays a READ below a write at a symbolic position, on a forked
chain or a consumer-boundary receiver, at a symbolic position, and for an array whose elements are
an input (one a symbolization reached, or whose shadow stands for a semantic value). The array's
identity node is built only when it roots a new state.

## 7. Wire handoff

**Leaf natives** (`VM/concolic/leafBroker.{hpp,cpp}`; `System.exportLeaf`, `System.mintLeaf`). A
leaf is one value of a message graph, addressed by the slot that holds it: `FIELD` (a
`java.lang.reflect.Field` of the parent instance), `ELEMENT` (an array and an `Integer`), `ENTRY` (a
`HashMap`, `LinkedHashMap`, `ConcurrentHashMap` or `Hashtable` and its key: identity, a String by
content, a box by value; the heap is walked with no member bound, `ContainerSupport::member_of`),
`POSITION` (an `ArrayList` or `ArrayDeque` and an `Integer`), `VALUE` (the leaf itself). Both run
inside a region or on a thread outside every region under an open workload session
(`ConcolicMngr::may_use_session_heap`, the rule `exportExpression` uses), need no `ThreadContext`,
and answer one JSON document (an expression table beside it) whose `status` names every refusal,
with a `reason`.

- `exportLeaf` peeks. It answers the slot's shadow (`source: SLOT`): a field shadow; for an element,
  an entry or a position what the container's recorded chain says (`ContainerSupport::
  element_answer`, `entry_answer`, `position_answer`): the value its newest write stored, a `READ`
  of the state when the chain cannot name one write (a symbolic position or key, an opaque node),
  nothing when the member is the heap's own. Else the leaf object's own expression (`OBJECT`; never
  a JVM-wide object's), else its typed constant (status `CONSTANT`; a String past the symbol-name
  bound states only `concrete`). It records no condition, read or version; it takes one event id
  (`exportEvent`). Refusals: `NO_SESSION`, `SLOT_MISSING`, `NULL_LEAF`, `UNSUPPORTED` (a leaf that
  is no primitive, box or String; a static field; an unmodeled container).
- `mintLeaf` states a decoded leaf as a template `{"parts":[{"literal":T} |
  {"hole":K,"label":L,"text":T}, ...]}` over fresh symbols: `NUM` (a primitive or box leaf's one
  part: a symbol of its sort), `DEC_INT`/`DEC_LONG`/`BOOL` (`toString` of an `I`/`J`/`Z` symbol; the
  text must be Java's rendering, `Long.toString(Long.parseLong(t)).equals(t)`), `STR` (a String
  symbol). A hole labelled `L` is `M_<T>_field_L` (`M_L'String'_field_L`) and states its
  `concreteValue`. A String leaf becomes `concat(parts)`, whose texts must be its content exactly,
  compared in UTF-16. The expression lands on the slot for a field (a `WRITE` version, as a
  putfield publishes) or an element (an INDEXED `WRITE`, the array named), and on the leaf object for
  a value, an entry or a position. A mint never puts an expression on a JVM-wide object and never
  replaces one; an object's expression is claimed in one step under the heap lock
  (`SessionSymbolicHeap::claim_object_expression`), so of two mints of one object (a String two
  decodes share) one lands and the other is `SHADOWED`. Refusals: `SHARED` (the landing object or
  the holder of the slot is JVM-wide), `SHADOWED` (what the mint lands on already carries an
  expression: the leaf object's semantic one -- a String's identity symbol is none -- e.g. a String
  a codec's cache shares, or a field slot with a shadow
  or an input owner's projection, or an element its array's recorded state names or an input array
  holds). A refusal of a located leaf states `landsOn` (`OBJECT` or `SLOT`): for `OBJECT` the
  caller stores a fresh equal object and mints again, a `SLOT` refusal stands. `TRACKED_CONTAINER`
  (an entry's or position's container has a state, an element is versioned, or a field is a tracked
  location), `TEMPLATE_MISMATCH`,
  `MALFORMED_TEMPLATE`, `NO_SESSION`, `SLOT_MISSING`, `NULL_LEAF`, `UNSUPPORTED`. A mint records no
  condition; on a thread inside a region it opens the admission gate. This JDK's
  `Integer/Long/Short/Byte.valueOf` box afresh, so a JVM-wide box is only a `Character` cache entry
  or `Boolean.TRUE/FALSE`; an enum constant is never a leaf (`UNSUPPORTED`) and, as a holder,
  `SHARED`.
- The codec runtime calls them (`runtime/CodecExport`, `HandoffMint#mintHoles`; IDENTITY.md §7.5);
  a `WIRE_FLOW` row still crosses through the expression broker.

**Expression broker** (`VM/concolic/expressionBroker.{hpp,cpp}`): `exportExpression` publishes the
live expression of an instance field and returns an opaque handle `(epoch << 32) | serial`;
`attachExpression` resolves a handle and installs the expression as a `ConsumerBoundaryExpression`
on the destination field (a container leaf becomes the destination container's state). Handles live
for the session: any region on any attached thread of that session can attach; a handle of another
session is `FOREIGN`. Statuses: `NO_ACTIVE_REGION -1`, `MISSING_METADATA -2`, `FIELD_NOT_FOUND -3`,
`NOT_SYMBOLIC -4`, `FOREIGN_HANDLE -5`, `UNKNOWN_HANDLE -6`, `SORT_MISMATCH -9`,
`UNSUPPORTED_TARGET -12`. An attach is a version of the destination (a container attach: a
`STATE_ATTACH` version, and one per tracked element of an array). The handoff is same-JVM: bytes
cross between nodes concretely, and the handle rides the message envelope (SYMBOL-SCOPE.md §6.3).

## 8. What the VM publishes

`jdk/src/share/classes/java/lang/System.java` declares 34 concolic natives (registered in
`jdk/src/share/native/java/lang/System.c`, implemented in `VM/prims/jvm.cpp`).
`runtime/ConcolicVmBroker` looks 25 of them up by reflection, so it loads on a stock JDK, and
`#requireCurrentCapabilities` refuses a replay plan before its workload starts when any is missing:
sessions, regions, context and event ids, `symbolize`/`symbolizeField`/`symbolizeExactField`,
`observeField`, `getSymbolicExpression`/`getSymbolicFieldExpression`, path-condition
pause/resume, branch events and range, `endConcolic`, `exportExpression`/`attachExpression`,
`getTrackedLocationVersions`, `installGuardedStoreSites`, `exportLeaf`/`mintLeaf` (§7; bound as
`ConcolicVmBroker#exportLeaf`/`#mintLeaf` with a `SlotKind` whose ordinal is the VM's). `markConcolicBranch` and the pause
natives are called by woven code (`CausynthPipeline.HookCatalog#concolic`). The broker mirrors the
statuses `OK 0`, `MISSING_METADATA -2`, `NOT_SYMBOLIC -4`, and its own `INVOCATION_FAILED -1001`,
`MALFORMED_RESULT -1002`, and names every status in the gap a refused export or attach files
(`ConcolicVmBroker#statusName`).

- Expressions are published as a DAG envelope (`VM/concolic/exp/expression.cpp`, iterative
  serializer); the engine keeps them in each session's `expressions.jsonl` (CONTRACT-SPEC.md).
- `getTrackedLocationVersions(afterEventId, maxBytes)` pages the version and read logs by each
  location's highest event: `nextAfterEventId` is one past the last emitted location's, so a
  resume neither repeats nor skips a location (`SFV`). A page is cut only between locations, once
  its text and table reach `maxBytes` (its first location goes whatever its size), and carries the
  expression table of what its locations name, last: every page repeats the closure its locations
  share. The engine hands each page to its publication thread as it is read, once fewer than four
  pages' text wait there undecoded, and decodes it there one location at a time
  (`contract/VmExpressionTable.Store#importRecords`), asking for `READ_OUT_PAGE_BYTES` pages
  (`runtime/SharedStateCapture`); a branch's path-condition window (`CONCOLIC_PATH_CONDITION_RANGE`,
  its conditions then the closure's table) is read the same way (`runtime/PathConditionWindow`).
  The table is the envelope's last member, compact, spelled `,"vmExpressionTable":{<schema,
  session, definitionCount>,"definitions":[<rows>]}}`, each row `{"_type":"VmExpressionDefinition",
  "sessionId":<s>,"expressionId":<n>,"expression":{...}}` in ascending id (`write_table`); a
  definition is one shallow object whose strings are escaped, so no row start occurs inside one.
  The importer reads the table off the text: a row of a node the store has expanded is skipped by
  its id, never scanned; a row whose ids do not read so is parsed whole; a table that does not close
  the envelope, a row holding more than one row, or a count the rows do not meet is refused. The
  store is locked only while a node expands. Each envelope is bounded by its own bytes
  (32 MB, `serializationTruncated` when cut), never by the page's. An envelope (`schemaVersion` 2:
  its read log states each read's version, §5.2) states `writerSetComplete` and,
  when false, `incompleteReasons` and `unnamedWriter`; an INITIAL's `initialSnapshot.stated` is
  true only for a stated count.
- A read node states `observedExact`, `writerSetComplete`, `unnamedWriter` (only when true) and
  `concreteValue` (a String past 4 KB
  as `{"_type":"TruncatedValue","length":n}`); a method-return symbol states `concreteValue` and
  `call: {holder, name, descriptor, arguments}`; a container query its chain may not decide
  states `concreteValue` and `answer` (§6).
- A region's summary (`finishConcolicRegion`) states no condition (`pathConditionAuthority`
  `VM_SELECTED_BRANCHES_V2`: a decision is a marked branch's own conditions, read by their indices),
  is read only for `aborted`, `abortReason` and `modelGaps` as a page's header is for its members
  (`runtime/ConcolicRegionRuntime#members`), and states its `modelGaps`: `{name, site}` per call a
  model ran on the run's own values though symbolic content reached it (§4: streams, application code
  a muted call with callbacks ran unhooked), once per name and site; `runtime/ConcolicRegionRuntime#modelGaps` files each as a DIAGNOSTIC `UNSTATED_VALUE`
  gap whose subject is the name.
- Natives no engine code calls: `getPathCondition`, `trackContainerExpression`,
  `getSharedFieldVersions`, `getSharedElementVersions`, `getSharedMapVersions`,
  `getConcolicRegionSummary` (only the smoke tests use them). `armSharedPrimitiveFieldRead` and
  `confirmSharedPrimitiveFieldRead` are refusals kept for `libjava`'s binding.

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
| `System.arraycopy`, `Arrays.copyOf` | hooked: element values into the destination's state (a stated word per element; past 16384 elements a shadowed destination's state is dropped and named), tracked destination elements versioned in one critical section with the copy (`VM/concolic/heapCopy.cpp`); an object copy that checks each element's store holds no lock across it: it names its tracked destination elements (`ARRAYCOPY_STORE_CHECK`, or `ARRAYCOPY_FAILED` when it will throw) |
| `Object.clone`, array `clone()` | hooked: the clone gets its own identity and the original's field shadows or state; a tracked field takes its newest version's value when the clone holds what it wrote (its word; a reference's shadow expression), else is concrete |
| `Unsafe` puts, CAS, `getAndAdd*`/`getAndSet*` (`ConcurrentHashMap` slots, `lazySet`, `AtomicReference`, `AtomicBoolean`, field updaters, reflective `Field.set`) on a shadowed object | hooked: versioned with the captured operand; a captured CAS answers `old == expected` over the value it compared as its native's result; uncaptured ones detected (`UNSAFE_WRITE_UNCAPTURED`) |
| `String` and `StringBuilder`, boxing, `HashMap`/`ArrayList`/... operations, atomic RMW | modeled (§4) |
| `Integer.parseInt`, `Long.parseLong` | detected and pinned (return symbol with its concrete value) |
| decimal and boolean renderings (`toString`, `String.valueOf`, `append`) | modeled: one `toString` op |
| radix, hexadecimal, char and floating renderings | detected (a named operation, not pinned) |
| a tracked scalar or reference changed by a write the hooks never saw | detected and pinned (`UNOBSERVED`, or the retained version that stored the word) |
| an array element a recorded write no longer describes | detected and pinned (concrete, `UNHOOKED_ELEMENT_WRITE`) |
| map `putIfAbsent`/`putAll`/`replace*`/`compute*`/`merge`/`replaceAll`/`removeIf` | modeled (§4, §6): a choice a guard, a callback's result and its side effects hooked; what a callback that did not run would have stored detected and named (an unknown cell, `CONTAINER_PINNED:`) |
| a `java.util.stream` pipeline over a modeled container | modeled (§4): its result a guarded chain, its stages' callbacks seeded; what no relation states detected and pinned (a `PIN`, or the run's result named `STREAM_PINNED:`); an unmodeled operation named and hooked as bytecode |
| a stream over any other source, a parallel stream | hooked (bytecode); a predicate's decision inside the JDK's sink is an unmarked branch, silently lost |
| list `removeIf` on a tracked container | detected (`writerSetComplete = false`); on an untracked one silently lost |
| stream `write(byte[])`/`readFully`, `ByteArrayOutputStream` | through arraycopy: hooked |
| a cached box, `Boolean.TRUE/FALSE`, an interned String returned by `valueOf` or a container | hooked: the value rides the result slot; the shared object stays clean |
| a mint (`symbolize*`, `mintLeaf`) on a JVM-wide object | refused: a box a field holds is minted on the field; a shared root, owner or holder is not minted, and the runtime names it by its cause (`RootMint#mintRefused`, `HandoffMint#mintTemplate`) |
| `Unsafe` volatile or object gets | the field shadow or nothing; a tracked location's get is not a versioned read |
| a native method with a symbolic argument (JNI, most JDK natives) | silently lost |
| `String.toCharArray`/`getBytes`/`getChars`, `new String(bytes)` | silently lost |
| `StringBuilder.reverse`/`appendCodePoint`, a padding `setLength` | dropped: the builder's next use states its concrete content |
| `StringBuilder.append` of a range of a `char[]` or a non-String `CharSequence` | modeled: the appended text as a constant, or a named operation over the sequence's own expression; the builder's earlier content stays |
| `StringBuilder.append(Object)` of an unshadowed non-String | silently wrong (appends `""`) |
| operations of an unmodeled collection | element fields hooked; the container relation silently lost |
| digests, MACs, ciphers, logging | silently lost by design (muted) |
| Jackson generator and bean writer, direct `ByteBuffer` | silently lost (muted or `Unsafe`) |
| a value handed to a thread outside every region | silently lost; its writes to tracked locations are versioned unattributed |
| a separate process | silently lost (no mechanism) |
| clocks, `Random`, `identityHashCode` | concrete natives; clocks become roots only through the Java-side mint |

## 10. Current limits

- Silent losses and silently wrong relations, as listed in §9.
- Decisions never recorded: `instanceof`; implicit-check exceptions (a null dereference of a
  symbolic reference, an out-of-bounds index, division by zero, a failed cast) are never branch
  outcomes; `multianewarray` dimensions; branches before a region's admission gate; symbolic
  branches the weave did not mark (they enter only the thread-wide condition, which the engine
  never reads). A version's guard holds only the innermost region's decisions.
- Re-pairable state is integral, wrapper and reference fields, modeled containers and
  Unsafe-written locations. A container read states no word, so it is never exact, and an unhooked
  mutation of a container is not detected.
- A container answer is typed by the object the run returned (`ContainerSupport::java_type`): a
  null answer is a reference, so a witness in which the same query answers a String or a box is
  outside its sort.
- A write from a muted or paused thread is unhooked (detected at the next read of a word it
  changed, not attributed).
- `symbolize` stops at depth 5; mint failures print to the console only; a null argument to a mint
  native aborts through `guarantee` (the leaf natives answer a status instead). Symbol names are
  truncated at 1024 bytes (a leaf template's literal past that bound is refused
  `LITERAL_OVER_SYMBOL_BOUND`); some model paths
  abort on unexpected shapes (`symbolicString.cpp`, `symbolicStringBuilder.cpp`,
  `symbolicBigDecimal.cpp`).
- Cost: every expression lives until session close under one global arena mutex; every in-region
  field access takes the heap lock; a tracked access takes its location's stripe once and the slot
  map's lock briefly; the path-condition byte bound (`-Dcausynth.vm.pathcondition.bytes`) counts
  reference bytes only.

## 11. Smoke tests

`third_party/OpenJDK-Concolic-Execution-Engine/scripts/causynth_smoke_test.sh` compiles the 68
`test/causynth/Region*Smoke.java` files and an slf4j probe, and runs each under `-Xint` with
`JDK_HOME` set to the image; `RegionPathConditionTruncationSmoke` runs again with the byte bound
unset, 0 and 8192. A test fails by throwing. The script is run by hand; neither `mvn test` nor
`run_engine.sh` runs it. Value movement has one smoke per hook (`RegionArrayCopySmoke`,
`RegionCloneSmoke`, `RegionUnsafeWriteSmoke`, `RegionSharedBoxSmoke`,
`RegionStringBuilderMutatorSmoke`, `RegionWrapperFieldSmoke`), and the versioning rules theirs
(`RegionTrackedRaceSmoke`, `RegionReadExactnessSmoke`, `RegionLoadedValueSmoke`,
`RegionVersionDefectsSmoke`, for a reference carrier `RegionReferenceSwapSmoke`, and for a
reference that only names its object `RegionNamedReferenceStoreSmoke`, §5.1, instance, static
and element); the engine's paused bookkeeping in `Thread.init` has `RegionInheritedStateSmoke`
(§2); the
collections by interface have `RegionConcurrentHashMapSmoke` (the Map contract, callbacks, a
tree bin), `RegionMapIterationOrderSmoke` (a snapshot's members in their class's iteration order),
`RegionWrapperViewSmoke` (a view or wrapper is its container), `RegionStreamSmoke` (stream
pipelines: filter, limit, map, an unmodifiable map's entries, count, anyMatch, a set, the pins and
the model gaps), `RegionIndexedSizeSmoke` (an INDEXED size over its size source, §6: an array of no constant
length past its element writes, a list's size past `set()` and at its `APPEND`/`REMOVE`),
`RegionModelGuardSmoke` (the pin/guard discipline, §6: each guarded choice, the
named unknown cells, no version for a call that changed nothing, an `equals()` match, answers
stated on query and array-element nodes, nothing added to the path) and
`RegionAtomicCarrierSmoke` (AtomicBoolean and AtomicReference as carriers); the leaf natives have
`RegionLeafBrokerSmoke` (every slot kind with and without a region, peeks that record nothing,
templates, `SHARED`, a region-less mint reaching a later region's path through `parseLong`, and
the one `toString` op); `RegionRedefineOnStackSmoke` attaches an agent to its own JVM and
retransforms `Object` while a thread waits in it, then collects (§1). No smoke test covers the
collections the VM does not model, a resize caught in flight, or anything across JVMs.
