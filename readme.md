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