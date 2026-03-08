# OTel Context Propagation — Coverage Reference

`GraphCheckerTransformer` now includes a context propagation phase (Phase 1) that runs **before** PropTracer instrumentation. When enabled via config, it detects async boundary call sites in the target bytecode and injects:

```jimple
$ctx     = staticinvoke <io.opentelemetry.context.Context: Context current()>();
$wrapped = interfaceinvoke $ctx.<io.opentelemetry.context.Context: T wrap(T)>($arg);
// original call uses $wrapped instead of $arg
```

This relies solely on the three `wrap()` overloads natively provided by `io.opentelemetry.context.Context`: `wrap(Runnable)`, `wrap(Callable)`, and `wrap(Executor)`.

Enable with: `context_propagation_enabled=true` in the `.properties` config.

## Supported

| Async Boundary | Detection Rule | Arg Wrapped | Wrap Type |
|----------------|---------------|-------------|-----------|
| `new Thread(runnable)` | `java.lang.Thread.<init>`, first param is `Runnable` | arg 0 | `Runnable` |
| `executor.execute(runnable)` | any method named `execute`, first param is `Runnable` | arg 0 | `Runnable` |
| `executor.submit(runnable)` | any method named `submit`, first param is `Runnable` | arg 0 | `Runnable` |
| `executor.submit(callable)` | any method named `submit`, first param is `Callable` | arg 0 | `Callable` |
| `scheduled.schedule(runnable, …)` | method `schedule`, first param is `Runnable` | arg 0 | `Runnable` |
| `scheduled.schedule(callable, …)` | method `schedule`, first param is `Callable` | arg 0 | `Callable` |
| `scheduled.scheduleAtFixedRate(runnable, …)` | method `scheduleAtFixedRate`, first param is `Runnable` | arg 0 | `Runnable` |
| `scheduled.scheduleWithFixedDelay(runnable, …)` | method `scheduleWithFixedDelay`, first param is `Runnable` | arg 0 | `Runnable` |
| `ForkJoinPool.execute/submit` | same method name rules as above | arg 0 | `Runnable` / `Callable` |
| `CompletableFuture.*Async(…, executor)` | declaring class `java.util.concurrent.CompletableFuture`, method ends with `Async`, last param is `Executor`/`ExecutorService`/`ScheduledExecutorService` | last arg | `Executor` |
| `Futures.addCallback(…, executor)` | declaring class contains `.Futures`, method `addCallback`, last param is Executor type | last arg | `Executor` |
| `Futures.transformAsync(…, executor)` | same, method `transformAsync` | last arg | `Executor` |
| `Futures.transform(…, executor)` | same, method `transform` | last arg | `Executor` |

Detection matches the **declared parameter type** of the call site's method reference, not the runtime type of the argument. Only application classes are scanned; JDK internals, OTel classes, and PropTracer are excluded.

## Not Supported

| Pattern | Reason |
|---------|--------|
| `CompletableFuture.supplyAsync(Supplier)` / `thenApply(Function)` / `thenAccept(Consumer)` / `thenCombine(BiFunction)` — variants **without** an explicit `Executor` arg | OTel `Context` has no `wrap(Supplier)`, `wrap(Function)`, etc. Runtime helper classes would be needed. |
| `Thread` subclasses that override `run()` directly (no `Runnable` passed to constructor) | No call-site arg to replace; would require injecting a context field into the subclass and rewriting its `run()`. |
| `java.util.Timer.schedule(TimerTask, …)` / `scheduleAtFixedRate(TimerTask, …)` | `TimerTask` is an abstract class; OTel has no native `wrap(TimerTask)`. A wrapper subclass would be needed. |
| `AccessController.doPrivileged(PrivilegedAction)` / `Subject.doAs(…)` / `UserGroupInformation.doAs(…)` | OTel has no native wrap for `PrivilegedAction` or `PrivilegedExceptionAction`. |
| `ExecutorService.invokeAll(Collection<Callable>)` / `invokeAny(Collection<Callable>)` | The `Collection` argument requires runtime iteration to wrap each element; not handleable at a single call-site arg. |
| `ForkJoinTask.fork()` | Takes no argument — the task itself is the receiver. Wrapping requires injecting context into the task object. |
| NIO `AsynchronousChannel` operations with `CompletionHandler` | Handler is registered separately from execution; detecting the correct site is complex. |
| RxJava / Project Reactor (`subscribeOn`, `publishOn`, `Schedulers.*`) | Not in the detection table. |
| Non-`Local` arguments at the detected position (e.g. `NullConstant`) | Silently skipped — only Jimple `Local` values can be replaced. |
| Double-wrap guard | No check for already-wrapped args; chained executor submissions may wrap the same Runnable multiple times. |

---

## Running GraphChecker on Apache Hadoop HDFS

Everything is driven by a single script:

```
experiments/hdfs/run_hdfs.sh
```

It sources `experiments/hdfs/conf/hdfs.properties` for all paths automatically —
no need to copy-paste directories or classpaths by hand.

### Prerequisites

| Requirement | Version | Notes |
|-------------|---------|-------|
| Java (JDK) | 1.8 | Soot requires JDK 8 (`rt.jar` / `jce.jar` under `$JAVA_HOME/lib/`) |
| Maven | 3.x | Build tool for GraphChecker and HDFS |
| Hadoop HDFS source | 3.3.4 | Path set in `hdfs.properties` → `system_dir_path` |

### Quick start (first time)

```bash
cd /path/to/GraphChecker/experiments/hdfs

./run_hdfs.sh build      # 1) build GraphChecker jar
./run_hdfs.sh compile    # 2) compile HDFS sources
./run_hdfs.sh instrument # 3) instrument HDFS classes in-place
./run_hdfs.sh test       # 4) run all unit tests (no recompile → uses instrumented classes)
```

To instrument and immediately run a specific test in one step:

```bash
./run_hdfs.sh run org.apache.hadoop.hdfs.TestDFSClientRetries
./run_hdfs.sh run org.apache.hadoop.hdfs.TestDFSClientRetries#testGetFileChecksum
```

### Command reference

| Command | What it does |
|---------|-------------|
| `./run_hdfs.sh build` | Build `target/GraphChecker-1.0-SNAPSHOT-jar-with-dependencies.jar` |
| `./run_hdfs.sh compile` | Compile HDFS main + test sources into `target/classes/` |
| `./run_hdfs.sh instrument` | Run GraphCheckerTransformer — rewrites `.class` files in `target/classes/` in-place |
| `./run_hdfs.sh test [Class[#method]]` | Run tests via `mvn surefire:test` — **skips recompile** so instrumented classes are used |
| `./run_hdfs.sh run [Class[#method]]` | `instrument` + `test` in one step |
| `./run_hdfs.sh restore` | Recompile HDFS to recover the original un-instrumented classes |

Each command prints `[Profiler] <command> took Ns` on completion.

### How it works

`run_hdfs.sh` sources `hdfs.properties` to read three bash variables:

| Variable | Value |
|----------|-------|
| `system_dir_path` | HDFS project root |
| `system_classes_path` | `$system_dir_path/target/classes` — instrumented in-place |
| `java_class_path` | Full HDFS dependency classpath (Maven `.m2` jars) |

Instrumentation invokes:

```bash
java -cp "<graphchecker-jar>:<java_class_path>" \
     edu.uva.liftlab.graphchecker.GraphCheckerMain \
     -i <system_classes_path> \   # input: compiled HDFS classes
     -x <java_class_path>    \   # Soot dependency resolution
     -C hdfs.properties      \   # GraphChecker config
     -o <system_classes_path>    # output: same dir → overwrites originals
```

Tests run via `mvn surefire:test` (not `mvn test`), which invokes the Surefire
plugin directly — skipping the compile phase so Maven cannot overwrite the
instrumented classes.

### Iterating

```bash
# Edit hdfs.properties or GraphCheckerTransformer, then:
./run_hdfs.sh build      # rebuild tool (only if Java source changed)
./run_hdfs.sh restore    # recompile HDFS to get fresh .class files
./run_hdfs.sh run org.apache.hadoop.hdfs.TestDFSClientRetries
```

### Configuration — `experiments/hdfs/conf/hdfs.properties`

Key properties to adjust:

| Property | Default | Description |
|----------|---------|-------------|
| `whitelist_pilotfunc_classes` | `org.apache.hadoop.hdfs` | Only classes whose name contains this prefix are instrumented |
| `blacklist_pilotfunc_classes` | `…protocolPB,…protocol.proto` | Name fragments excluded from instrumentation |
| `entry_classes` | `…NameNode` | Recovery entry point |
| `startpoint_methods` | `…NameNode#main` | Starting method for static analysis |
| `context_propagation_enabled` | `true` | Inject OTel `Context.wrap()` at async boundaries |