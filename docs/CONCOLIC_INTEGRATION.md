# Concolic integration contract

主设计与验收标准见 [README.md](../README.md)。本文只记录 Java runtime 与 custom-JDK
之间当前唯一的 wire contract。

> 范围：本文是当前 wire contract，目标架构见 [../README.md](../README.md)。
> 「Worker isolation」中「一个 custom-JDK 进程只允许一个 active concolic context」
> 属于 README Phase 1 的改造范围（以 attach/detach 线程成员关系取代
> single-active-region mutex），不代表目标架构。

## Execution identity

一次 worker 执行由 `taskId` 标识：

```json
{
  "taskId": "TASK.<query>",
  "goalId": "GOAL.OUTPUT_RELATION.<demand>",
  "goalKind": "OUTPUT_RELATION_CLOSURE",
  "regionId": "REGION.3",
  "sourceKey": "node#epoch0",
  "occurrenceId": "node#epoch0/region/REGION.3#1",
  "relationKey": "node#epoch0/REGION.3",
  "rootSelector": {
    "method": "<Producer: int compute()>",
    "ordinal": 1
  }
}
```

`goalKind` 只有 `OUTPUT_RELATION_CLOSURE` 与 `TARGET_REACH_CLOSURE` 两种：同步调用
不切分调用方，所以一次 region occurrence 只有一条 relation。不接受 `regionInstanceId`、
singular `requestedOutput` 或独立 upstream activation。

## Runtime calls

Java instrumentation 使用以下最小接口：

```text
startConcolicRegion(regionId, taskId)
symbolize / symbolizeField / symbolizeExactField
markConcolicBranch
getConcolicBranchEvents
getConcolicPathConditionRange(startIndex, endIndex)
getSymbolicExpression / getSymbolicFieldExpression
snapshotContainerExpression / trackContainerExpression
exportExpression / attachExpression(handle)
pauseConcolicPathCondition / resumeConcolicPathCondition
finishConcolicRegion
endConcolic
```

region summary 不再内联整条 path condition，也不含任何 segment/watermark 成员：
selected branch witness 只带 `conditionIndices`，需要谓词时用
`getConcolicPathConditionRange` 按区间读回。该 native 单独绑定，与已删除的
native 分组，否则一次分组失败会静默降级整条 witness 通道。

Runtime 在 observation bookkeeping 前暂停 PC，完成 engine expression/summary 读取后结束
context。pause 期间执行的 Gson、null check 或 logging 不允许污染程序 PC。

## Exact branch event

每个被选 branch 在原 bytecode branch 之前调用 VM marker。VM event 与 Java mapping 必须
一致：

```text
siteId
occurrence
observed outcome/successor
new PC suffix indices
code position
```

Importer 只接受 exact event 拥有的条件。普通 Boolean branch 可被 Worklist 翻转；
multiway switch 必须保留 successor identity，不能压成一个任意 Boolean。

## Input materialization

`ExecutionTask.inputActions` 是 runtime 唯一输入目录。每个 action 指向：

- root receiver field path；
- root argument 或 argument field path；
- primitive/string/reference root value；
- array/container object root。

同一 port 只由一个 action materialize。runtime object identity 只用于在当前 task 中定位，
不进入跨执行 query identity。

nullable reference field允许在 concrete seed 为 null 时建立 symbolic field shadow；
若 normal output 仍为 null 且 VM 无法返回该 field 的 symbolic expression，该 path 对该
output fail closed。

## Output capture

root return 由 region exit 读取。字段 OUT 在每个正常出口插入一次 exact field-path read：

```text
captureBindingId
outputPort
outputCell
fieldSignature
fieldOwner
fieldValue
```

插桩把 exact leaf owner、field name、JVM descriptor 和 concrete value 一并交给
`getSymbolicFieldExpression(owner,name,descriptor,value)`。VM 直接读取该字段在当前
replay 结束时的 shadow；shadow 为空时才构造 exact concrete primitive/String/null
表达式。capture identity 不含 assignment site 或 occurrence，也不根据 seed path
预选写点。

异常出口不产生普通 output capture。

## ContainerRelation

custom-JDK 为每个 active context 维护：

```text
sym_rid -> current ContainerRelation state
cursor sym_rid -> next fixed iterator position
```

表达式 wire shape：

```json
{
  "_type": "ContainerRelation",
  "shape": "INDEXED|ASSOCIATIVE",
  "operation": "STATE|READ|WRITE|SIZE|...",
  "_java_type": "JVM descriptor",
  "receiver": {},
  "arguments": []
}
```

`STATE` 是 DAG 根：

- indexed `STATE(receiver,length)` 保留真实或 symbolic allocation length；
- associative `STATE(receiver)` 使用 activation-local reference identity。

array/List/Map operation 的 concrete result 会形成 equality observation。成功的 indexed
访问还记录 bounds。mutation 将 state table 原子替换为新的 DAG 节点。region 正常
退出时，runtime 对实际 array/Collection/Set/Map 值调用
`snapshotContainerExpression(...)`，随后 `getSymbolicExpression(container)` 返回
该 replay 的最终 container state；因此输出不依赖 assignment-site capture。

Java 侧没有第二份 container event ledger。

## Symbolic expression handoff

一次同一 workload JVM 内跨线程/逻辑节点的传值由 VM expression broker 承担，
Java 侧只是桥；live handle 不能跨真实 JVM 地址空间：

```text
exportExpression(owner, declaringClass, fieldName, descriptor) -> handle
attachExpression(owner, declaringClass, fieldName, descriptor, handle)
    -> exportEventId
```

`attach` 成功即表示接收方的位置**就是**发送方的表达式；session ledger 用一条
`VALUE_HANDOFF(exportEvent, attachEvent)` 记录这对事件，这是唯一的传播权威；session
session 生命周期统一回收 live handle。桥本身
不产出任何 edge artifact、不做 export×receive 配对、不做 tuple narrowing、不恢复
delivery ordinal，也不做 fallback matching。普通 interaction trace 只保留具体消息
correlation 与 request/response half 来观测拓扑；handoff bridge 不复制
`exchangeId` / `attemptId` / `direction` / `leafPath` payload，更不把它们当 join key。

失败的调用写一条命名 gap（`rpcHandoffGaps`），由 importer 收进 alignment gaps；
成功但没有任何 case 能声明其接收端口的 handoff，同样在 importer 处被命名，而不是
静默丢弃。

## Engine result

每次结束写一条：

```json
{
  "event": "CONCOLIC_REGION_RESULT",
  "schemaVersion": 1,
  "taskId": "TASK...",
  "exitKind": "NORMAL|THROW",
  "unresolvedInputs": [],
  "symbolizedInputs": [],
  "branchMappings": [],
  "outputCaptures": [],
  "rootOutputExpression": {},
  "engineSummary": {}
}
```

`engineSummary.aborted=true`、非空 unresolved、capture cardinality 错误或 exact branch
event 错误使 Importer 拒绝该 row。后续阶段不再重复解析 VM event stream。

## Worker isolation

一个 custom-JDK worker 拥有一个 fresh workload session。同一 RPC/状态依赖组的
selected region contexts 可以在该 session 的多个线程上共同执行；它们需要共享同一
symbolic heap、broker 和 event ledger。互相独立的 replay obligations 由 coordinator
放到多个 fresh JVM worker 并行执行，每个 worker 使用独立目录。

合并只接受完整、已归一化的 case/拓扑 delta，不跨 worker 共享 VM heap、
shadow state、raw event id 或 path-condition recorder。
