# Concolic integration contract

主设计与验收标准见 [readme.md](../readme.md)。本文只记录 Java runtime 与 custom-JDK
之间当前唯一的 wire contract。

## Execution identity

一次 worker 执行由 `taskId` 标识：

```json
{
  "taskId": "TASK.<query>",
  "goalId": "GOAL.OUTPUT_RELATION.<demand>",
  "goalKind": "OUTPUT_RELATION_CLOSURE",
  "regionId": "REGION.3",
  "regionInstanceId": "REGION.3@producer#call2",
  "rootSelector": {
    "method": "<Producer: int compute()>",
    "ordinal": 1
  }
}
```

不接受 `activationId`、singular `requestedOutput` 或独立 upstream activation。

## Runtime calls

Java instrumentation 使用以下最小接口：

```text
startConcolicRegion(regionId, taskId)
symbolize / symbolizeField
markBranch
getPathCondition / getBranchEvents
getSymbolicExpression
getRegionSummary
endConcolic
```

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

一个 custom-JDK 进程只允许一个 active concolic context。并行 coordinator 启动多个 JVM
worker，每个 worker 使用不同 `taskId` 和 output file。共享 worklist 只合并完整
`PathObservation`，不共享 VM heap、shadow state 或 path-condition recorder。
