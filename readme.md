# GraphChecker

GraphChecker 从静态数据流、一次真实运行和逐 region concolic replay 中构造
`region.in -> region.out` 关系，再沿动态 read-from 图组合成一个交给 Z3 的公式。
最终问题只有一个：

> 在 Java 语义、已观测跨线程顺序和各 producer 的完整输出关系下，目标 exception
> 是否可达？

当前实现面向固定顺序的 shared-field RPC workload。两个或多个 producer 可以并发，
consumer 在 producer 结束后各读取一次共享字段。分析不把线程调度本身当成符号变量。

## 工程原则

1. 正确性优先于代码行数；不为了达到数字删除不可推导的证明证据。
2. 不过度设计：只实现真实 workflow 立即需要的抽象。
3. 不过度校验：同一不变量只在其 trust boundary 校验一次，后续阶段消费 typed
   carrier。
4. schema 原子切换：writer、Java reader、shell reader 同时更新，旧 artifact 直接
   拒绝，不双写、不 fallback。
5. 一个事实只保留一个 canonical carrier。可由 canonical object 推导的镜像字段删除。
6. 修 bug 必须修语义模型，不为某个 fixture、site ID、字段名或 JSON 形状加特判。
7. fixture workload 是端到端语义门槛；测试协调使用固定次数和固定先后顺序，不引入
   `while (true)` 或不受限调度。

## 唯一生产流程

```text
annotated target exception
        |
        v
SeedBackwardStaticAnalyzer
  static_dataflow_edges.jsonl
        |
        v
SymbolicRegionPlanner
  symbolic_regions.jsonl
  symbolic_region_edges.jsonl
        |
        v
instrumented seed execution
  causynth-trace.jsonl
        |
        v
RuntimeRegionPlanner
  RegionInstancePlan
        |
        v
ConcolicScheduler
  ExecutionTask
        |
        v
parallel custom-JDK workers
  PathObservation
        |
        v
ConcolicSummaryImporter + RegionPathWorklist
  closed RelationSummary
        |
        v
ConcolicSmtComposer
  candidate.smt2
        |
        v
Z3: sat | unsat
```

JSON 只出现在 artifact 边界。生产链中的主要 carrier 是：

- `StaticRegion`：region 的方法、input/output port、branch 和 canonical edge。
- `OutputClosureContract`：一次下游 demand 所需 outputs 及每个 OUT 的 backward slice。
- `RegionInstancePlan`：一个真实 region invocation 和其 execution goals。
- `ExecutionTask`：一个 goal 的一次可执行 replay。
- `PathObservation`：一个 task 的 PC、branch occurrence 和 region-end outputs。
- `RelationSummary`：同一次 producer invocation 的 guarded output cases。

## Region、Activation 与 Goal

一个 `regionInstanceId` 对应一个 Activation envelope。它表示一次真实 region
invocation，而不是一个 branch 或 output。

```json
{
  "regionInstanceId": "REGION.3@producer#call2",
  "closureGoals": [
    {
      "goalId": "GOAL.OUTPUT_RELATION...",
      "kind": "OUTPUT_RELATION_CLOSURE"
    },
    {
      "goalId": "GOAL.TARGET_REACH...",
      "kind": "TARGET_REACH_CLOSURE"
    }
  ]
}
```

旧设计为同一 invocation 复制 `ACT.UPSTREAM.*`、`ACT.PATH.*`，并把 branch flip 和
output capture 当作互斥 activation。该设计已删除。

`(regionInstanceId, goalId)` 标识一个语义 campaign，`taskId` 标识其中某次具体
custom-JDK 执行。branch flip 是 output campaign 内部的路径枚举任务，不是新 activation。

Workflow 只使用两种相对角色：

- `TARGET`：包含目标 exception reach goal 的 campaign；
- `PRODUCER`：沿 runtime-confirmed read-from edge 反向可达 TARGET 的 output
  campaign，包括为其他 producer 提供输入的递归 producer。

不存在 `ARRAYVALUE`、`MAPVALUE` 或 `UPSTREAM_N` 这类 workflow 身份。稳定
`campaignId` 由 `regionId + regionInstanceId + goalId` 生成，目录和调度不依赖 Java
字段名、container 类型或 producer 在依赖图中的深度。

## Output closure

对下游请求的每个 OUT，Planner 做一次 backward dependency closure：

```text
requested OUT
  -> inputPorts
  -> relevant branch sites
  -> methods
  -> causalEdgeIds
  -> one region-end capture endpoint (field output)
```

只影响 debug 字段、无关计数器或无关 branch 的代码不进入该 OUT 的 slice。Worklist
只翻转：

```text
branch.siteId ∈ outputSlice.sites ∪ outputSlice.staticSites
```

### 多输出

同一个下游 demand 可以请求同一 producer invocation 的多个 output port：

```text
requestedOutputs = {outX, outY}
joint execution scope = slice(outX) ∪ slice(outY)
```

每个 OUT 仍保留独立 slice 和 capture endpoint，但只运行一个共享-PC campaign。每个
merged case 同时含所有 outputs：

```text
case C0:
  guard = ...
  outX = ...
  outY = ...
```

Composer 只能原子选择整个 case，不能把不同 replay、不同输入或不同 producer instance
的 `outX` 与 `outY` 拼接。任一 member 不完整则整个 joint demand fail closed。

### Field-sensitive object flow

对象作为方法参数传递时不降级成一个不透明 reference。静态 slice 保留精确字段路径，
例如：

```text
compute()
  -> resolve(envelope)
  -> envelope.state.flag.enabled
  -> envelope.state.enabledValue
```

参数别名仍由 receiver identity 关联，字段由真实声明签名关联。继承引用
`<Derived: int base>` 会规范成实际声明它的 `<Base: int base>`；静态 edge、插桩选择、
runtime materialization 和 native exact-field API 全部使用这个 canonical identity。
同名隐藏字段则保持两个不同 identity，不能因为 Java 字段名相同而合并。

构造函数和初始化方法若位于 target 的动态 provenance 中，会产生普通 upstream output
relation。因此 `producer.field = 0`、嵌套对象叶子和初始 container state 不再成为任意
existential input。它们与 producer relation 一起组合；这会排除只靠伪造初始化值才能
成立的 SAT。

## Region-end output semantics

字段 OUT 不绑定某个赋值 site，也不绑定 seed trace 的 occurrence。所有候选路径在 region
正常出口读取一次字段当前 symbolic expression：

```java
if (condition) {
    b = x;
} else {
    b = y;
}
```

两条 replay 产生：

```text
condition   -> b_out = x
!condition  -> b_out = y
```

merge 后：

```text
b_out = ite(condition, x, y)
```

如果某条路径不写 `b`，出口读取自然得到 `b_in`，即 frame condition。若一条路径多次写
`b`，出口读取自然得到最后一次动态写之后的表达式。不再维护 write-site candidate、
last occurrence、heap-effect discharge 或 assignment-site capture。

正常返回值由 root exit 直接捕获。异常退出没有普通 output；exception path 与 normal
output relation 分开。

## Container symbolic V2

### 目标

array、Map、List、Set、Queue 和 view 不再由 Java Planner 枚举元素、entry 或 snapshot。
custom-JDK 在 activation 内维护 shadow state，Java 侧只消费唯一的 `ContainerRelation`
表达式 DAG。

```text
Java object identity
      |
      v
activation-local shadow state
      |
      +-- READ / WRITE
      +-- SIZE / IS_EMPTY / CONTAINS
      +-- APPEND / INSERT / REMOVE / REMOVE_AT / CLEAR
      +-- VIEW / ITERATOR / HAS_NEXT / NEXT / KEY / VALUE
      |
      v
region-end ContainerRelation
      |
      v
shared ContainerSmtCodec
```

Path solver 与 Composer 都调用同一个 `ContainerSmtCodec`。select/store/size、
Map presence/value/order、Java Boolean、String 和 integral width 只有一份 SMT
lowering。

### 唯一 IR

VM 序列化的表达式本身就是 IR：

```json
{
  "_type": "ContainerRelation",
  "shape": "ASSOCIATIVE",
  "operation": "PUT",
  "receiver": { "... previous state ..." },
  "arguments": [{ "... key ..." }, { "... value ..." }]
}
```

不存在第二份 `containerRelations` event array，也不存在 Java
`containerElementFieldBindings`、`finiteMapSnapshots`、`engineArrayInputBindings`
或 container 专用 `dynamicFieldBindings`。

### 两种 state shape

`IndexedState` 用于 array/List/Queue：

```text
size: Int
elements: Array<Int, Value>
```

`AssocState` 用于 Map/Set：

```text
size: Int
present: Array<Value, Bool>
values: Array<Value, Value>
order: Array<Int, Value>
position: Array<Value, Int>
```

`Value` 统一承载 primitive、String 和 reference。Java `int/long` 宽度随
`ContainerSmtCodec.Term` 传播，算术仍使用 `java_int_wrap/java_long_wrap`，不能退化为
无界数学整数。

### 初始状态

V2 不构造全量 container snapshot。

- 已存在 array 的 length 固定为真实 concrete length。
- region 内 `new T[n]` 的 array state 直接携带 symbolic `n`。
- successful indexed read/write/iterator step 自动加入 `0 <= index < size`。
- Map/List/Set 的 size、lookup、contains、iterator key/value 按实际执行惰性加入精确
  equality。
- 未被当前 output closure 读取的元素不会被枚举，也不会进入 artifact。

因此容器可以在 region 内符号化 mutation 并改变 size；但已有 Java array 的长度不会在
原地变化。若程序用 symbolic `n` 新建另一个 array，新 array 的长度可以变化。

### V1 精确支持集

支持：

- array：length、load、store；
- List：get、set、add、insert、remove(index)、contains、size、isEmpty、clear、
  iterator/hasNext/next/remove；
- Queue：offer、poll、peek、element、remove()；
- Set：add、remove、contains、size、isEmpty、clear、iterator；
- Map：get、put、remove(key)、containsKey、size、isEmpty、clear；
- Map view：entrySet、keySet、values、iterator、hasNext、next、getKey、getValue、
  iterator remove、backed-view clear。

暂不支持并 fail closed：

- `Map.putAll/putIfAbsent/replace/replaceAll/compute*/merge`；
- `Map.remove(key,value)`；
- `List.remove(object)`、`listIterator(int)`；
- `ListIterator` 的额外 mutation 和其他 view mutation；
- reflection、native container API、direct/off-heap buffer；
- 依赖具体 HashMap bucket、TreeMap comparator 或 JVM 内部布局的语义。

这些边界是为了保持小而准确的 Java collection contract；不为尚未出现的 API 预建第二套
模型。

### Container output

region-end capture 对 primitive field、普通 object field 和 container field 使用同一
机制：

```text
read exact field path at normal exit
  -> System.getSymbolicFieldExpression(owner, field, descriptor, value)
  -> scalar expression or final ContainerRelation
```

因此 capture 不关心最后执行了哪个 `put`、array store 或 field assignment。无 mutation
时直接读取 field shadow 并得到 pre-state；本路径写入 concrete String/null/primitive
时得到精确常量；有多个 mutation 时得到最终 shadow state。这里查询 field shadow 而不是
只查询 `value` 对象 identity，因而不会把 no-write frame condition 错降级为 seed
concrete value。

VM 将“字段从未获得 shadow”和“字段已被本次 replay 的 concrete `putfield/putstatic`
覆盖”区分开。后者保留一个 activation-local written marker；普通 `getfield` 和 Zero
fast accessor 都不会再按需重建入口 `FieldAccessExpression`。因此固定循环或 clamp
把 symbolic 字段写成 concrete 值后，后续 branch 与 region-end capture 看到的是新值，
不会产生只能在 SMT 中成立、Java replay 无法执行的伪路径。

## Parallel concolic exploration

custom-JDK 本身保持单 context，不在一个 JVM 内并行修改 symbolic state。并行发生在进程
层：

```text
shared concurrent worklist
  -> worker JVM 1: replay query A
  -> worker JVM 2: replay query B
  -> ...
  -> worker JVM N: replay query N
```

每个 worker 有独立 custom-JDK、heap、PC 和 output file。Coordinator 用 canonical
query key 去重，按 wave 合并新 paths，再生成下一批 flips。worker 数可按服务器核心数设得
很高；同一 query 只允许一个 accepted result。

并行只改变调度顺序，不改变：

- branch relevance；
- path query identity；
- region/output closure；
- merged case identity；
- SAT/UNSAT 公式。

## Correctness boundary

必须保留且不能用行数目标删除：

- target exception 的稳定 annotation identity；
- 每个 OUT 的 backward slice 和 causal edge IDs；
- branch witness、exact VM path-condition event 和 occurrence；
- `regionInstanceId/goalId/taskId/queryKey` lineage；
- shared-field writer/reader event sequence；
- receiver/value object identity 和 read-from evidence；
- joint-output 同 case 相关性；
- `relationallyComplete` 与所有 gaps；
- composed artifact SHA-256。

不保留：

- 固定 authority 文本、恒定 Boolean、数组长度镜像、纯计数；
- 可由数组大小或 canonical object 推导的字段；
- 只供旧 shell/测试检查、没有生产消费者的 JSON；
- deep-copy-then-strip、同一 payload 多次 decode、兼容 adapter。

## Debug artifact 顺序

流程失败时按首次出现 gap 的阶段向前看，不要从最终 SMT 猜原因：

1. `analysis/symbolic_regions.jsonl`
   - requested OUT、input ports、sites、methods、capture endpoint。
2. `runtime/concolic_region_plan.jsonl`
   - 正确的 region instance 是否有 `OUTPUT_RELATION_CLOSURE` goal；
   - admission blockers。
3. `campaigns/target/<campaignId>/execution_task_plan.jsonl`
   - target 的 `taskId`、branch contract 和 replay root。
4. `campaigns/producer/<campaignId>/execution_task_plan.jsonl`
   - producer 的 `taskId`、symbolize actions、branches、output closure。
5. 同一 campaign 目录中的 `concolic_region_results.jsonl`、
   `concolic_region_summaries.jsonl` 和 `import_diagnostics.jsonl`
   - custom-JDK abort reason、unresolved input、PC、region-end expression 和
     Importer 拒绝原因。
6. 同一 producer campaign 目录中的 `path_closure.json`、
   `path_exploration_records.jsonl` 和 `merged_summary.jsonl`
   - `CLOSED/GAPPED`、具体 gap、每个 case 的 guard 与所有 output expressions。
7. `candidate/candidate_composition_manifest.json`
   - unresolved edge、sort/expression gap 和输入 summary SHA。
8. `candidate/candidate.smt2`
   - 只在 manifest `CANDIDATE_READY` 且 gaps 为空后直接运行 Z3。

常见错误定位：

```text
producer path list not executable
  -> execution_task_plan + raw result

worklist does not close
  -> path-worklist + rejected replay records

AmbiguousJavaIntegralBinaryWidth
  -> merged output expression + ContainerSmtCodec term width

composition is not structurally complete
  -> candidate_composition_manifest.gaps
```

## Build 与验证顺序

大规模 schema cutover 采用以下顺序，避免边写边用旧 fixture 反向塑造新框架：

1. 完成全部 production writer/reader 切换；
2. 删除旧路径和旧 schema；
3. 静态搜索确认 retired field 不再有生产消费者；
4. 编译 Java；
5. 编译 custom-JDK/HotSpot；
6. 运行少量 contract 测试；
7. 并行运行 13 个真实 custom-JDK/Z3 fixtures；
8. 按 artifact lineage 修复，直到既定 SAT/UNSAT 全部稳定；
9. 记录生产代码行数、各阶段耗时和 fixture 结果；
10. milestone commit 并 push。

测试代码总量保持几十个聚焦 contract 测试；不维护数百个锁定整份 JSON 字节形状的单元
测试。fixture workload 不为迁就实现而改语义。

## 本轮重构验收

本轮完成必须同时满足：

- 一个 region instance 只有一个 Activation envelope；
- execution goal 统一使用 `ClosureGoalKind`；
- execution identity 只叫 `taskId`，不再用 `activationId` 承载；
- field OUT 在 region exit 捕获最终 expression；
- joint outputs 共享 PC 和 merged case；
- container 只存在一个 `ContainerRelation` IR；
- solver/Composer 共用 `ContainerSmtCodec`；
- 旧 element/entry/snapshot/dynamic binding/heap transformer 路径全部删除；
- Java 与 custom-JDK 编译通过；
- 13 个真实 fixtures 的 Z3 SAT/UNSAT 与语义基线一致；
- 用户的 manual workload 本地修改保持不变；
- 最终 commit 和 push 完成。

40K–50K 生产 Java 是合理的代码规模方向，不是验收捷径。若正确、general 的实现确实需要
更多代码，保留代码；若旧代码已无生产消费者，则删除，不保留“以后也许有用”的 fallback。

## 2026-07-27 final validation

本轮冻结后的生产 Java 为 43,606 行，相对 PR 0 记录的 81,084 行减少 37,478 行
（约 46%）。`three-thread-rpc/run.sh` 从旧的 1,618 行降为 1,385 行；剩余 Shell
负责可见的 stage orchestration、artifact lineage、并行 worker 和带完整上下文的失败
诊断，不再复制 Planner/Importer/Composer 的 schema 语义。

最终 gate：

```text
custom-JDK API smoke              23/23 PASS
Maven contract tests             105/105 PASS
fixed-RPC stress, 5 x 20         100/100 PASS
original real workflows           13/13 PASS
container tricky workflows         5/5 PASS
manual campaign-layout workflow    UNSAT PASS
```

stress 的每个 `PASS` 同时要求：四行 concrete truth table 正确、真实 custom-JDK/concolic
流程结束、Z3 SAT/UNSAT 与预期一致、两条 shared-field RPC producer binding 都进入最终
composition。原 13 个 workflow 的最大并发初跑中有 3 个 JVM 因 fixture 固定 10 秒
`join` 在系统 load 超过 100 时超时；这 3 个在串行、不修改代码和 fixture 的条件下均
通过，因此它们被记录为资源调度超时，而不是语义失败。
