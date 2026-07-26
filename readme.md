# GraphChecker：region concolic execution 与 SMT composition

GraphChecker 从静态数据流、运行时跨 region 证据和逐 region concolic execution 中构造
`region.in -> region.out` 关系，再沿 region graph 递归组合成一个可直接交给 Z3 的 SMT。
当前维护的验证矩阵是通用三线程 RPC fixture 及其 cross-method、multitype、
dependent-scalar、container，以及四个互补的 `UNREACHABLE` 变体。后者要求完整流程
生成的 SMT 由 Z3 判定为 `unsat`。

## 项目定位

这是一个纯学术的软件工程与程序分析项目，研究静态分析、运行时分析、concolic execution、
symbolic state propagation、guarded symbolic merging 和 SMT composition。核心流程只接受
配置、程序证据和类型化 artifact，不包含面向某个应用或 bug 的公式。

旧 HDFS 实验 adapter、冻结静态 catalog checkpoint、领域 port mapper 和显式 contract
registry 已退出维护并从仓库删除；通用 RPC、container、Java 语义和 fail-closed evidence
检查继续由 maintained workload matrix 覆盖。

## 三线程候选模型 milestone（2026-07-21）

generic 三线程流程当前自动完成 annotation 定位、静态切片、runtime discovery、逐 producer
路径闭合、candidate SMT composition、Z3 求解和有限 Boolean-root 枚举（其余 scalar root
保持 existential）。终态 artifact 使用统一的
`state=CANDIDATE_READY`、`trustState=CANDIDATE_ONLY`，并将求解结论写成
`reachability=REACHABLE|UNREACHABLE`。result manifest 绑定 SMT、composition manifest、
relationship catalog 和 Boolean model 的路径、大小及 SHA-256，但不会声称已经得到可信最终
结果。`run.sh all` 是 `candidate` 的别名。

旧的半成品 trusted/natural-replay 发布路径已经删除。将候选输入在完整 workload 中自然
replay、绑定实际 exception observation，并据此升级 trust state，是本文唯一保留的 TODO。

## 当前参考工作负载

### 用 annotation 精确标记 exception target

应用代码不再通过 `target.yaml` 中的 exception class 触发一次全局 throw/source 搜索。
Java 8 不允许直接给 `throw` statement 加 annotation，因此目标标记放在 exception
construction 的 type-use 位置：

```java
import edu.uva.liftlab.graphchecker.annotation.CausynthExceptionTarget;

if (a > b) {
    throw new @CausynthExceptionTarget("three-thread-rpc")
            BugReachedException(a, b);
}
```

`@CausynthExceptionTarget` 使用 `RetentionPolicy.CLASS`，不产生运行时行为。GraphChecker
直接读取 classfile 的 `NEW` type annotation。目标的稳定语义身份由 declaring class、方法名与
JVM descriptor、exception type，以及同一方法中同类型 construction ordinal 共同组成；source
line 和 bytecode instruction index 只用于诊断与 classfile/Jimple 对齐，不属于语义身份。该身份
被唯一解析到对应的 Soot method/Jimple throw，静态 backward slice 因而直接从这一点开始，
不再扫描源码寻找同名 exception，也不再把同类型的其他 throw 当成候选。

当一个输入 class tree 有多个 marker 时，`target.yaml` 只用稳定 id 选择一个：

```yaml
exception_target_id: three-thread-rpc
```

未提供 id 时必须恰好只有一个 marker；缺失、重复或无法唯一映射到 Jimple throw 都会
fail closed。旧的 exception-name 搜索、`seed_variables`、`seed_function` 及其配置 alias
均已删除。annotation 只消除目标定位上的重复确认；跨线程 producer、read-from、顺序、
对象/值 identity 和 runtime instance 仍必须由静态/运行时证据验证。

三线程 fixture 位于
`src/test/java/edu/uva/liftlab/graphchecker/fixtures/ThreeThreadRpcWorkload.java`：

```java
// Thread 1
int a = 0;
if (b1) a = 1;
else a = -1;

// Thread 2
int b = 10;
if (b2) b = 0;
int var = externalIntInput;
if (var < 10) var = 10;
b = b + var; // Java int wrap semantics

// Thread 3
int a = getRPCFromA();
int b = getRPCFromB();
if (a > b) throw new BugReachedException(a, b);
```

它使用三个真实 Java worker thread。两个 producer 并发执行并通过 `RpcBus` 发布值；两者
结束后 consumer 才读取值，因此 producer 与 target 的动态 region 不重叠，同时仍保留
真实的跨线程 publish/read 边界。

这个 fixture 不再 hard-code RPC mapping。Soot 首遍只生成 candidate、插桩点和 frozen
static graph；runtime 确认具体 root/class/thread call closure 后，在 frozen graph 上做一次
小范围 demand re-slice。跨线程 producer/consumer 关系由 shared-field receiver identity、
write-before-read、region instance、runtime evidence 和 producer path replay 自动验证。

工作负载的具体路径语义由自动生成的 guarded summaries 和 Z3 truth table 给出。例如：

```text
Producer A: b1 = false -> a = -1
            b1 = true  -> a = 1

Producer B: base = ite(b2, 0, 10)
            boundedVar = ite(var < 10, 10, var)
            b = java_int_wrap(base + boundedVar)

候选 truth table / reach condition:
  从生成的 root-input catalog 自动枚举，不由 fixture 提供公式
```

完整的终态 candidate artifact 集合由代码自动写入：

```text
target/three-thread-rpc/candidate/candidate.smt2
target/three-thread-rpc/candidate/candidate_composition_manifest.json
target/three-thread-rpc/candidate/symbolic_relationship_candidates.json
target/three-thread-rpc/candidate/candidate_boolean_model.json
target/three-thread-rpc/candidate/candidate_result_manifest.json
```

这些 schema-2 JSON 使用 `state`、`trustState` 和（求解完成后）
`reachability` 表达结果；不再保留旧的状态、完整性、eligibility 或自然回放能力镜像字段。
它们只表示 candidate composition 已完成且 Z3 已检查，不能冒充经过最终自然回放验证的用户
报告。

## 核心抽象

### Region

系统不再把 region 分成 protocol、lifecycle 等领域类型。这里只有两种角色：

- bug 所在的 target region；
- target 的所有直接或递归上游 region。

所有上游 region 都是 producer。一个上游 region 的 `in` 可以来自另一个更上游 region
的 `out`，因此 composer 可以一直递归到没有上游 producer 的 root input。

### `region.in`

`region.in` 是该 region 关系中所有可 symbolized 的 live-in 值：它们在输出切片中被读取，
但其定义不属于当前 region。参数、局部定义入口、field/array 读取、调用返回值和受证的
VM placeholder 都可以成为 input。一个 region 可以有多个 input。

静态分析负责找全候选 input，并为同一语义值建立 canonical port。运行时证据负责把候选
绑定到具体 activation、对象、调用和定义位置。不能因为某个 input 在一条路径上未使用，
就把它从整个 region 接口中删除；它应被记录为该路径 inactive。

容器输入保留 selector 与 scalar leaf 两层身份。对于
`array[i] -> Map.put(key, element) -> element.field.field`，数组索引和元素对象只用于定位，
有序 `fieldPath` 的末级 primitive/String 值才成为 symbol。若 producer 没有偶然调用该
leaf getter，静态 output demand 仍可把 leaf 反投影到 exact container snapshot；运行时必须
再确认数组元素 identity、逐级 owner、declared field signature 和类型，不能把整个对象引用
当作 scalar symbol。

maintained `containers` workload 还要求 `MapProducer.input1`、`input2` 成为两个 existential
`int` root：两者分别在小于 10 时 clamp 到 10，随后按 Java `int` wrap 语义求和。跨方法发现的
`producer#field:inputN` 端口只有在唯一 exact static chain、相同非零 runtime owner identity、
有序 field-read cut 且中间没有 leaf write 时，才 canonicalize 到声明字段端口。最终闭合关系为
array producer 2 cases、map producer 10 cases；两个 Boolean root 的四行 candidate truth table
均为 `sat`，因为两个 `int` root 在每一行仍按 existential 求解。

`unreachable-parity` 是复杂 container-field 回归：array 与 Map producer 都读取
`state.guard.enabled`、`state.metrics.left`、`state.metrics.right`，包含 clamp、短路条件和
后置分支。RPC 拓扑不变，每个 producer 只向自己的 shared field publish 一次，consumer
也只读取各 field 一次。完整关系的输出域分别是奇数 `{-1,1,3}` 与偶数 `{0,2,4}`；两个
Boolean root 之外的四个 `int` field root 保持 existential，因此四行 Boolean truth table
必须全部由真实组合 SMT/Z3 证明 `unsat`，不能靠 fixture 常量或测试脚本直接判定。

另外五个 `UNREACHABLE` workload 保持相同的 shared-field RPC 边界，只把 producer
内部的数据传播做深：

- `unreachable-correlated-fields` 从 nested `seed/delta` 计算值，并在一次 publish 中写
  correlated `left/right`；联合 output closure 必须让两个字段共享同一 relation case，
  再与独立 `limit` producer 组合。
- `unreachable-nested-object` 让 Boolean 与两个整数穿过
  `Envelope -> Payload -> leaf` 和 helper 参数，最终两个 producer 的输出域分别保持
  odd/even。
- `unreachable-inherited-alias` 让同一 derived object 经两层 alias helper 传播，同时读取
  inherited `base` 与 derived `delta`，其 bounded value 永远低于另一个 producer 的 floor。
- `unreachable-mutated-object` 先从 nested object 读取并保存 scalar snapshot，再计算 bounded
  output，随后覆写对象字段；这些后续 heap write 与 requested output 无关，不能污染 closure。
- `unreachable-long-fields` 让 nested `long base/adjustment` 和 Boolean leaf 穿过 helper，
  两个 producer 的完整输出域分别保持 odd/even。

五个 workload 都先让 producer rendezvous，再用 latch 固定 publish 先后；两个 producer
终止后才启动 consumer。每个 shared field 只写一次、只读一次，consumer 的读取顺序固定。
同步等待本身不带 timeout branch，避免把测试协调逻辑误切入 output closure；超时仍由
harness 的 `join` 负责。

当前没有把“直接通过 shared field 传递对象引用”列为 UNSAT 门禁。对未证明 heap relation
的对象字段，Composer 会安全地保留 existential over-approximation，因此可能得到 `sat`。
上述对象测试只在 producer 内验证深字段/alias 传播，RPC 边界仍使用可精确证明的 primitive
shared field。

### `region.out`

`region.out` 不是“方法返回值列表”，也不是 region 中所有被写过的变量。它只包含会流入
下游 `region.in` 的定义值。返回值、field 写、array 写或传给下游调用的值都可能是 out；
与任何下游 input 无关的临时值不应成为 out。一个 region 可以有多个 output。

静态 dataflow 给出候选 `out -> in` 边；跨线程/RPC 关系由程序中的调用、publish/read
与共享状态自动发现，最终边需要具体 runtime 顺序、对象或完整值 fingerprint 证据确认。

### Region relation

每次 concolic execution 只记录一条真实路径。多条已验证路径合并为：

```text
R_region(in, out) =
    (guard_0(in) && out = expr_0(in))
 || (guard_1(in) && out = expr_1(in))
 || ...
```

每个 merge case 保存求解所需的 guard、output/state transformer，以及来源
`(regionInstanceId, goalId, taskId)`；raw runtime result、完整 region plan 和重复 branch
trace 不会复制进 merged relation。Merger 只能合并已执行并通过 importer 的 canonical
summary；不能把未探索路径当作不存在。

## 自动分析流程

```text
classfile exception annotation
  -> 唯一 target NEW/method/Jimple throw
Soot annotation-directed 静态分析
  -> 从 target 反向得到 region.in/out、output slice、候选 region edges
运行时 discovery trace
  -> region instance、thread context、branch event、精确 read-from
RegionInstancePlan
  -> 每个动态 region instance 一个 envelope，内含 bounded ClosureGoal
RegionClosureExplorer
  -> seed task -> pending PathQuery -> Z3 input -> custom-JDK replay -> PathObservation
Relation reduction
  -> producer 的 R_region(in, out)，或 target 的完整 reach condition
Upstream composer
  -> 沿受证 region edge 将上游 out 绑定到下游 in
Z3
  -> candidate SMT、Boolean truth table、候选 reach condition
Candidate manifest
  -> hash-bind SMT、composition、reach model 和 relationship candidates
TODO: 自然传播可信升级
  -> SAT 输入自然 replay；绑定实际 target exception 后才能发布可信结果
```

### Closure goal，而不是 branch goal

branch flip 不是顶层分析目标，只是构造完整 relation closure 的内部路径枚举手段。系统只
保留两种一等语义目标：

| ClosureGoal | 产物 | 闭合条件 |
| --- | --- | --- |
| `OUTPUT_RELATION` | demanded output 的完整 guarded transformer | 所有 output-relevant frontier 已执行或证明不可行，且无 gap |
| `TARGET_REACH` | 精确 target exception/event 的完整可达条件 | target method 范围内所有相关 frontier 已执行或证明不可行，且无 gap |

目标运行模型是：

```text
RegionInstancePlan
  └─ ClosureGoal
       ├─ PathQuery
       ├─ ExecutionTask
       ├─ PathObservation
       └─ RelationSummary
```

一个动态 `regionInstanceId` 只对应一个 `RegionInstancePlan` envelope。当前
`activationId` 是历史 schema 为同一个实例复制 `ACT.UPSTREAM.*`、`ACT.PATH.*` 时产生的
镜像身份；新 reader/writer 切换后应退休，而不是再作为语义 key。envelope 可以包含多个
closure goal，但每个 goal 保留自己的 input action、branch/site slice、edge binding 和
admission，不能把不同 goal 的 readiness 或证据粗暴 union。

身份分工固定为：

```text
regionInstanceId  动态 region invocation
goalId            一个 bounded relation closure
queryKey          一个待求解的 path frontier
taskId            一次真实 custom-JDK execution
```

`(regionInstanceId, goalId)` 标识语义 campaign，但不足以标识一次执行：同一 output closure
通常会产生多个 path query 和 replay。runtime object token、Map/array selector、PC、capture
与 raw result 必须以 `taskId` 为执行 scope；case identity 和 relation selector 则根据
task-independent 的 canonical path semantics 生成，不能因 worker 或 retry 改变。

Producer campaign 不需要让 custom JDK 同时符号执行三个线程。系统对一个 region instance
执行多个 task，汇总为一个或多个 closure relation；跨 region 关系仍在 composer 中组合。

### `pending` 与 campaign

`pending` 不是 Z3 的 `unknown`，也不是尚未启动的线程。它是某个 `ClosureGoal` 内尚未被
真实 execution 覆盖的 `PathQuery`，身份包含 goal、路径 prefix、branch site、occurrence、
目标 outcome 和 runtime bindings。branch flip 只存在于这个 worklist 层，不会制造新的
Activation 或 ClosureGoal。

一次 execution 会加入一条 observed path。若该 trace 已自然覆盖某个 flip 的目标
frontier，该任务直接视为 covered；否则 planner 才让 Z3 求一个新输入并 replay。不同
prefix 下的同一 branch 仍是不同任务。campaign 重复这个过程，直到：

```text
observed paths > 0 && pending = 0 && gaps = []  ->  state = CLOSED
```

没有 closure seed 时 manifest 显式报告 `state = NOT_STARTED` 和 gap；不能把
零条 observed path 或缺失 manifest 当成 closed。只有 `CLOSED` 才允许生成 guarded
relation。这样不会在已经观察到 branch 两侧后再产生无意义的反向 replay。

一条路径上的 output-relevant branch 可能因为更早的约束而被 VM concretize。此时它没有
可翻转 predicate，但也不能在仍有 pending bridge task 时立刻终止 campaign。worklist 先把
它记为 `deferredObservations`；后续只有相同 closure goal、相同 site 且相同 occurrence
出现精确 symbolic witness 时才覆盖它。若所有 task 都已终止而仍没有该 witness，observation
才升级为 blocking gap，状态为 `GAPPED`。不同 loop occurrence 不能互相冒充证据。

### 复合 target guard

Java 的 `if ((a > b && c > d) || x > y)` 不会在 bytecode/Jimple 中保留为一个原子
branch；短路求值会产生多个二元 branch。仅使用传统 control dependence 中“恰好一个
successor 能到 throw”的规则会漏掉 OR 左侧这种两个 successor 都仍可能到达 throw 的
决策。target exception 的静态 seed 因此使用一个直接的 bounded rule：

```text
branch 位于精确 target method
&& branch 至少一个 successor 能到精确 annotated throw
```

这个规则只用于 `TARGET_REACH` closure。producer output slice 仍使用原有控制依赖规则，
避免扩大 output closure。运行时从一次未强制 seed 开始，只翻转 target goal 中实际出现的
symbolic branch witness；普通退出和抛异常的 replay 都是合法路径证据。worklist 闭合后，
`TargetReachPathQueryBuilder` 只保留 `normalExit=false` 且 exception type 精确相同的 imported
summary，最终异常条件为：

```text
fatal =
    OR(
      AND(path_0 的完整 PC),
      AND(path_1 的完整 PC),
      ...
    )
```

因此前置 `if`、AND/OR 的每个短路 operand 以及到达 throw 前的完整 prefix 都进入 SMT；
不会再把一次 branch flip 的局部条件误当成完整异常条件。若闭合路径中没有一条抛出精确
目标异常，`fatal=false`，后续 composer/Z3 仍正常运行并给出 UNSAT。该算法复用现有
custom JDK 的单路径 PC capture，不需要在 custom JDK 内实现并行或新 guard lowering。

新增的 `compound-target` 与 `unreachable-compound-target` fixture 使用三个确定顺序的线程、
两个 nested-object Boolean producer、六个 primitive shared fields，并保证每个字段只写一次、
只读一次。前者固定真值表为 `00=unsat, 01/10/11=sat`；后者在同一复合外层 guard 中加入
矛盾内层 guard，四组 Boolean valuation 全部必须由真实 Z3 判定 `unsat`。

### Path campaign 失败时看哪里

`run.sh` 失败时会直接打印负责下一步定位的 artifact，不需要从完整 JSON stdout 猜原因：

```text
target-campaign/region_path_closure.json
target-campaign/observed_path_summaries.jsonl
schedule/branch_queries.jsonl
target-campaign/current/task-<queryKey>/stderr.log
target-campaign/current/task-<queryKey>/path_flip_solver_result.json
target-campaign/current/task-<queryKey>/concolic_region_results.jsonl
target-campaign/current/task-<queryKey>/concolic_import_diagnostics.jsonl
target-campaign/current/task-<queryKey>/path_replay_verification.json
producer-campaign/<channel>/current/region_path_manifest.json
producer-campaign/<channel>/current/region_path_worklist.jsonl
producer-campaign/<channel>/current/task-<queryKey>/stderr.log
producer-campaign/<channel>/current/task-<queryKey>/path_flip_solver_result.json
producer-campaign/<channel>/current/task-<queryKey>/concolic_region_results.jsonl
producer-campaign/<channel>/current/task-<queryKey>/concolic_import_diagnostics.jsonl
producer-campaign/<channel>/current/task-<queryKey>/path_replay_verification.json
```

先看 manifest 的 `state`、`gaps` 与 `deferredObservations`。单 worker 失败时，脚本还会打印
对应 queryKey、solver/verifier 状态和 `stderr.log` 尾部；custom JDK 在写出 JSON 前崩溃时，
`stderr.log`、task 目录中的 `hs_err_pid*.log` 和 replay task plan 仍足以定位执行阶段。
成功 wave 会按既有 policy 清理，失败 wave 始终保留。

## Runtime 与 custom JDK

Scheduler 只把 ready `PathQuery` 编译成引用
`(regionInstanceId, goalId, taskId)` 的小型 execution task；它不再决定 TARGET/OUTPUT
二选一的语义，也不复制完整 region plan。GraphChecker runtime 维护 task-scoped 的
region/thread context；custom JDK 使用 thread-local concolic context，并限制同一时刻的
engine-backed owner，避免其他应用线程或 GraphChecker 自身 bookkeeping 污染当前 path
condition。

每个可求解的二元 branch 只产生一个不可变的 typed `BranchWitness`。它包含稳定的
`site + occurrence`、源 execution 实际满足的 outcome/predicate，以及唯一允许的 `VM_PC`
evidence。wire value 本身没有 self-hash；需要稳定去重时，worklist 对 canonical value
计算 key。`BranchReplayContract.flip()` 是唯一可以推导相反 polarity 的位置：它保留有序
prefix、翻转一个 source witness，并丢弃旧 suffix。producer/target worklist、solver、
execution task、静态插桩、runtime、importer 和 verifier 都传递或解析同一个 contract；target
replay 允许普通退出与精确异常退出，闭合后再按异常类型筛选完整 PC。各阶段不再重建旧式
target、prefix、negated-condition 或 scheduled-target 副本。精确 VM event 若没有对应 PC，
只能作为 observation 和诊断信息，不能制造 predicate、witness 或 flip；`switch` 也仍是
独立的 successor-aware observation，不伪装成二元 branch。

源 path condition 中夹在 branch 之间的 array-load 或 method-relation 节点不是 branch
evidence。schema-3 worklist 把它们放入另一个不可变的 typed `SolverPathContext`，并保留
原始 `summaryPcIndex`；该对象只接受 `_array_expr` 和 `MethodExpression`，遇到没有 witness
的 Boolean predicate 会直接拒绝。solver 分别断言 context 与 contract，runtime replay 只
消费 contract。它同样没有 self-hash；stable key 由使用方从 canonical 内容计算。这样既不会
丢掉求解所需的非 branch 关系，也不会再把同一个 branch witness 复制成多套
path-condition/target/prefix JSON 来相互确认。

invocation ordinal 只表示同一 receiver-class/thread context 中的第几次调用，用于定位动态
region instance，不代表程序语义，也不进入稳定 worklist key。

跨 RPC/codec/SASL 的值传播使用独立的 runtime-confirmed `EQUALITY` binding：它要求两端
canonical port、exact region instance、完整 value fingerprint 和 writer-before-reader 顺序，
但不要求序列化前后的对象 identity。它与共享 field 的 `READ_FROM` 保持不同 relation kind，
composer 按 edge、kind、instance 和 runtime witness 精确选择，二者不能互相替代。

Producer 的模型只能 materialize 到静态分析找到并由 instrumentation 确认的真实定义位置。
路径翻转只通过输入模型和不可变 replay contract 表达，runtime 记录实际观察到的 branch
witness。当前输出到候选模型为止；未来的可信升级必须让 target 保持 observation-only，
不得给 consumer 注入 model、返回值或 branch outcome。

Map 变异只通过 VM `MethodExpression` 导入通用的 `MAP_PUT` / `MAP_REMOVE` /
`MAP_CLEAR` / `MAP_PUT_ALL` heap transformer。直接 `Map.remove(key)` 受支持；maintained
contract 刻意不支持 `Iterator.remove()` 变异：精确 static causal-edge `invoke` 可以识别该
调用，但 VM `HashMap.removeNode` 证据无法证明对应的 application call 与 current entry。
importer 因此报告 `INCOMPLETE_ITERATOR_REMOVE_APPLICATION_PROVENANCE`，并令
`relationallyComplete=false`，而不是通过 side channel 猜测 backing map/key 或生成不可信
SMT。旧的子模型完整性镜像字段已删除。iterator `next()`、entry/key/value 读取、有限 Map
snapshot 和深层字段绑定不受影响。

## 递归 SMT composition

Composer 从 fatal query 反向遍历 region graph。若下游端口 `D.in.j` 由上游端口
`P.out.k` 提供，它会建立受证绑定，并把 `R_P` 接入 `R_D`。若 `P.in` 仍来自其他 region，
相同步骤继续递归；root input 才保留为最终 SMT 的自由输入。

对三线程 workload，组合语义等价于：

```text
a = ite(b1, 1, -1)
b = java_int_wrap(ite(b2, 0, 10) + ite(var < 10, 10, var))
bug = (a > b)
```

但这些文本没有 hard-code 在 workflow 中；它们来自 Producer A 的两条和 Producer B 的
四条 path summary、两条 runtime-confirmed RPC edge 和 target branch condition。外部
`int var` 保留为 root input，Boolean 投影对它作存在量化。最终 SMT 由
`ConcolicSmtComposer` 生成，`BooleanReachConditionExtractor` 再对自动发现的 Java Boolean
root 做有限真值表投影并生成 canonical DNF。

Composer 采用 fail-closed 规则：缺 summary、未闭合 relation、未绑定端口、unsupported
expression 或来源不唯一时，只能产生 incomplete manifest。结构完整且经 Z3 检查的输出仍是
candidate；当前流程没有 final/trusted 发布状态。

## 证据与来源检查

不同层的权限必须分开：

| 层 | 可以证明什么 |
| --- | --- |
| 静态分析 | region 接口、定义/使用、候选跨 region 边和插桩位置 |
| runtime trace | 具体 activation、thread、对象、顺序、publish/read 与 branch occurrence |
| concolic summary | 一条真实路径上的 guard、symbolic expression、concrete output |
| guarded merge | 已验证路径集合上的完整 `R_region(in,out)` |
| composer + Z3 | 在上述关系和声明 bounds 下的跨 region reach condition |

Manifest 中的来源检查不是密码学“证书系统”，而是防止把本次 composition 的输入、输出和
其他 run 的 artifact 混用。Importer 在生成 canonical summary 前验证 raw execution；
Merger 只接受 closed path worklist 中的 admitted summaries。Composer 消费 merged relation
及其 source ids，但不会重新加载 raw result、原始 activation，再做一套重复的外部认证。
branch 层只解析并消费 `BranchWitness`、`BranchReplayContract` 和 `SolverPathContext` 的
canonical typed value；这些对象不带 self-hash。

Composition manifest 是跨文件绑定的唯一 authority：它对本次 CLI 实际读取的 regions、
fatal query、summary 和生成的 SMT 记录路径、长度和 SHA-256；写出 relationship catalog
后，再把该 artifact 绑定回 manifest。schema-2 relationship catalog 只保存
`schemaVersion`、`kind`、`trustState` 和 `relationships`，不再复制 fatal identity、stage、
artifact hash、eligibility 布尔值或第二个 `compositionBindingId` 来与 manifest 逐字段互证。

自动 topology discovery 不能把程序没有执行出来的 equality、cache、expiry、membership
或 codec 语义冒充 runtime fact。自动 composition 只接受静态、runtime 和 concolic 阶段
共同满足的证据门槛；手写 RPC mapping 不再是输入协议。

## 配置与命令

通用入口是 `run_engine.sh`。路径、JAR、被分析项目、class path、custom JDK、Z3、静态与
runtime 产物位置都来自 `key=value` 配置文件，不应写死在命令行或 Java 代码中：

```bash
./run_engine.sh \
  --config experiments/generic/three-thread-rpc/workflow.properties \
  config

./run_engine.sh \
  --config experiments/generic/three-thread-rpc/workflow.properties \
  validate
```

相对路径由 `workflow_path_base` 统一解释；也可以使用 `@config/`、`@project/` 和
`@repo/` 前缀。配置文件按数据解析，不会被 shell `source`。详细键和环境变量覆盖见
`experiments/generic/README.md`。

基础回归：

```bash
mvn test
experiments/generic/test_workflow.sh
```

三线程自动工作流：

```bash
experiments/generic/three-thread-rpc/run.sh help
experiments/generic/three-thread-rpc/run.sh clean
experiments/generic/three-thread-rpc/run.sh all
```

`all` 串联 build、annotation-directed static analysis、trace、discovery、target seed、
producer campaigns、candidate composition、Z3 solve 和 candidate manifest。成功时会生成
`candidate/candidate_result_manifest.json`；它不是 trusted result。

producer path exploration 默认使用 `nproc` 个独立 custom-JDK worker。每个 worker
拥有私有 result、tmp 和日志目录；同一 wave 全部成功后才由单一 coordinator 发布。
串行 debug 或显式高并发可以分别使用：

```bash
CAUSYNTH_CONCOLIC_JOBS=1 experiments/generic/three-thread-rpc/run.sh all
CAUSYNTH_CONCOLIC_JOBS=64 experiments/generic/three-thread-rpc/run.sh all
```

2026-07-24 的 container 实测中，jobs=1/8/40/64 都闭合相同的 48 条路径并得到
相同语义投影与最终 `sat`；耗时分别约为 870、233.56、203.35 和 202.77 秒。
单 wave 最多只有 16 个 pending task，因此 64 没有优于 40，默认值保持 `nproc`。
六个 maintained fixture 的并行矩阵耗时 231.77 秒，五个预期 `sat` 与一个预期
`unsat` 全部通过。完整设计、正确性边界和测量口径见
`docs/parallel_concolic_execution_plan.txt`。

## 关键实现

| 组件 | 职责 |
| --- | --- |
| `SymbolicRegionPlanner` | 静态 region、live-in/live-out、output slice 和候选 edge |
| `RuntimeRegionPlanner` | 每个动态 region instance 构造一个 plan，并挂载 bounded closure goals |
| `RegionClosureExplorer` / `RegionPathWorklist` | 在 goal 内规划 frontier、稳定去重，并在 CLOSED 时生成 guarded relation |
| `ConcolicScheduler` | 把 ready query 编译成小型 execution task，不承担 closure 语义 |
| `ConcolicPathFlipSolver` | 精确求解一个 query，为 SAT frontier 产生 replay task input |
| `ConcolicRegionRuntime` | 执行 task，记录 task-scoped PC、capture、heap 与 branch observation |
| `BranchWitness` / `BranchReplayContract` | 二元 branch 的唯一不可变 observation/replay authority |
| `SolverPathContext` | 与 branch authority 分离的、有位置的 typed 非 branch solver constraints |
| `BranchReplayObservationValidator` | 在 runtime 与 Importer 边界验证有序 witness 流 |
| `ConcolicSummaryImporter` | 将 raw custom-JDK 结果严格导入 `R(in,out)` path summary |
| `ConcolicSmtComposer` | 递归绑定上游 out 与下游 in，生成 composed SMT |
| `BooleanReachConditionExtractor` | 调用 Z3 枚举 Boolean roots 并生成 reach condition |
| `run_engine.sh` | 配置驱动的通用阶段编排 |

custom JDK 位于 `third_party/OpenJDK-Concolic-Execution-Engine`。三线程端到端 fixture、拓扑、
配置和阶段脚本位于 `experiments/generic/three-thread-rpc`。

## 架构重构设计与实施计划

### 目标、口径与优先级

本节是 GraphChecker Java 实现的权威重构计划。重构只统计
`src/main/java` 的手写生产代码；测试和 fixture 不计入行数目标。maintained fixture 下的
test workload 不得删除或改弱；唯一例外是经明确授权后把
`cross-method-fields` 的冗余 110-path Cartesian product 缩成 4 个语义路径，同时增加真实
joint-output 相关性门禁。普通回归测试则随旧实现一起合并、去重和删除，最终只保留几十个
覆盖真实 contract boundary、关键 fail-closed 行为和端到端语义的高价值用例。
2026-07-23 的基线为 81,594 行生产 Java，其中
`ConcolicRegionRuntime`、`ConcolicSummaryImporter`、`RuntimeRegionPlanner`、
`ConcolicSmtComposer`、`SymbolicRegionPlanner` 和 `SeedBackwardStaticAnalyzer`
六个文件共 56,231 行。

行数不是独立的正确性指标。重构的优先级固定为：

1. maintained fixture 的最终 Z3 `sat` / `unsat` 结果正确；
2. runtime、summary 和 composition 继续 fail closed；
3. 每个语义事实只有一个 authority 和一个 completeness 计算点；
4. 不过度校验、不过度设计：只在真实 trust boundary 校验一次必要不变量；
5. 删除兼容路径和重复实现，降低生产代码与认知负担；
6. 删除只锁定 JSON 形状、私有实现细节或重复排列组合的低价值回归测试；
7. 在不牺牲前四项的前提下缩小代码规模。

“fail closed”不等于每一层重复证明全部事实。codec 只验证 wire schema、identity、scope 和
无 partial decode；Planner/Scheduler 证明计划确实对应静态与运行时 endpoint；Runtime
记录执行证据；Importer 在消费边界独立验证执行结果。中间层不得重新实现上下游已有的
语义分析，也不得为了类型化而建立一套平行 framework。每个新增 abstraction 或 validation
都必须能指出它替代的旧代码，或它所封堵的具体错误传播路径；否则不应加入。
普通测试不得成为第二套 specification：同一 trust boundary 优先使用一个表驱动测试，
真实 workflow 语义由 maintained fixture 和实际 Z3 `sat` / `unsat` 结果负责兜底。

保留全部 heap、Map、array、dynamic-field、Java primitive/FP/String、跨线程 read-from 和
runtime identity 功能时，可信的最终目标是约 45,000–55,000 行生产代码。约
30,000–35,000 行是 bounded-scalar 核心的规模目标，不是全功能仓库的硬性上限。拆大文件、
把代码搬到生成目录、压缩格式或删除诊断都不计作有效减量。

### 优先架构切换：以 relation closure 为中心

下一轮首先删除由“单一 capture goal”造成的伪 activation。当前
`RegionCaptureGoal = TARGET_BRANCH | OUTPUT_CLOSURE` 迫使 Planner 为同一动态 invocation
复制 `ACT.UPSTREAM.*`，Scheduler 再按 goal 二选一；path replay 又复制 `ACT.PATH.*`，bundle
继续嵌套完整 activation row。这些对象不是新的 region invocation，只是不同的语义 demand
或执行尝试。新版本不再保留 bundle：跨 region 的 producer relation 先独立闭合，最终由
Composer 组合；一次 custom-JDK execution 始终只执行一个明确的 task。

新的唯一顶层计划是 `RegionInstancePlan`：

```json
{
  "kind": "REGION_INSTANCE_PLAN",
  "regionInstanceId": "REGION.3@call2",
  "regionId": "REGION.3",
  "rootSelector": {},
  "instanceAdmission": {},
  "catalogs": {
    "actions": [],
    "branchObservations": [],
    "dynamicDemands": [],
    "edgeBindings": []
  },
  "closureGoals": [{
    "goalId": "GOAL.<semantic-hash>",
    "objective": {
      "kind": "OUTPUT_RELATION",
      "outputClosure": {}
    },
    "actionIds": [],
    "branchObservationIds": [],
    "dynamicDemandIds": [],
    "edgeBindingIds": [],
    "admission": {}
  }]
}
```

同一 input port 在不同 output slice 中可能需要不同 field path、array observation 或
container binding，因此 envelope 不能简单地“每个 port 只存一个 symbolize row”。
`actions` catalog 按完整语义 payload 生成稳定 `actionId`，goal 只引用自己需要的 action
variant。branch observation、dynamic demand 和 edge binding 同样只存一份 canonical row，
goal 通过 ID 引用。禁止增加 goal-local override/fallback；如果 payload 真正不同，就必须是
两个不同 catalog item。

`instanceAdmission` 只表示动态 invocation/root replay 是否存在；goal admission 只表示其
slice、read-from、capture 和 closure 是否完整；task admission 只表示本次 model、
materialization 和 replay 是否可执行。三层 ownership 不互相复制 readiness boolean，也不
用一个 goal 的 READY 掩盖另一个 goal 的 gap。

实际 worker 输入是小型 `ExecutionTask`，不是另一个 activation：

```json
{
  "kind": "CONCOLIC_EXECUTION_TASK",
  "taskId": "TASK.<attempt-hash>",
  "regionInstanceId": "REGION.3@call2",
  "goalId": "GOAL.<semantic-hash>",
  "phase": "SEED | PATH_REPLAY",
  "queryKey": "QUERY.<frontier-hash>",
  "modelAssignments": [],
  "replayContract": {}
}
```

task 不复制 root selector、output closure、symbolize action、branch catalog 或完整 edge
binding；instrumentation/runtime 通过 `regionInstanceId + goalId` 解析 plan，再以 `taskId`
开启一次 active token。raw result 和 imported summary 统一携带：

```text
executionRef = (regionInstanceId, goalId, taskId)
```

retry 或同一 query 的另一 worker 必须得到不同 `taskId`，否则 activation-local object
token、Map.Entry selector、array identity、PC 和 capture 可能跨执行串联。相反，`caseId`
按 canonical path semantics 计算，使相同路径不会因为 task/worker 不同而产生不同 SMT
selector。reachability bundle 只包含 execution-task reference，不嵌套整个 region plan。

#### Output relation 的闭合语义

若 `field1` 是 demanded output：

```java
if (x > 10) {
    field1 = x + 1;
} else if (x == 0) {
    field1 = 7;
}
```

正确产物不是某次 flip 的结果，而是所有相关正常路径的 transformer：

```text
field1_out =
  ite(x > 10, x + 1,
    ite(x == 0, 7, field1_in))
```

未写 `field1` 的正常路径必须有经过证明的 frame condition
`field1_out = field1_in`。异常、超时或不退出的路径没有普通 `field1_out`，必须以独立
exit/exception observation 参与 closure completeness，不能伪造成普通 output case。
worklist 只翻转 `outputSlice.sites/staticSites` 中的 branch；它不再判断某条 replay
会命中哪个写点，也不维护“最后一次写入”。每条正常 replay 统一在 Region 出口读取 OUT，
由 symbolic heap 直接给出该路径的最终 expression；与 closure 无关的 branch 不进入
frontier。

primitive instance-field 的 frame condition 使用现有 relation contract，不另建 frame
subsystem：静态 output slice 加一个与 output cell 完全相同的 `HEAP_PRESTATE` input；
runtime discovery 通过精确 putfield receiver identity 和引用型 getfield event，求得唯一
bounded `region root -> ... -> field` 路径；custom JDK 在 region 入口 symbolize 该真实字段。
`captureBindings` 不再表示 assignment site。primitive/reference field output 只保留
`demanded field + exact receiver + FieldPathSpec + normal-exit coverage`。Instrumentation
在 Region/root activation 的每个正常出口读取一次该字段当前值，并把此时 custom-JDK
symbolic heap 中的 expression 记录为该 replay 的最终 OUT：

```text
PathObservation {
  normalExit,
  output[field1] = symbolicExpression(read(receiver.field1))
}
```

因此多个静态写点、同一写点循环执行任意次数以及 branch flip 后 occurrence 变化都不需要
特殊处理；Region replay 完成时字段是什么 expression，output 就是什么 expression。零写
路径也无需反推“没有哪个写点执行”：入口真实字段已经 symbolize，出口读取自然得到
`field1_in`，从而形成 `field1_out = field1_in`。正确性门槛只剩精确 receiver/field path、
入口 prestate materialization，以及所有正常出口均安装 capture；异常、超时或非正常退出不
产生普通 output。删除 seed occurrence、assignment execution count、last-write event
ledger 和相关 fallback。reference/container output 继续走既有 identity、heap-effect 和
Map/array transformer contract，不能被 primitive frame 规则猜测替代。

同一次 invocation 中被同一个 downstream demand 共同使用的 `outX/outY` 属于一个 joint
`OUTPUT_RELATION` goal。每个 task 原子捕获完整 output set，每个 relation case 使用同一
guard/case selector；任一 member 缺 capture 或 proof，整个 joint goal fail closed。不能把
分别来自不同 task/path 的 `outX` 与 `outY` 拼成一个不存在的程序状态。

`TARGET_REACH` 使用同一个 explorer，只在 reduction 时保留精确异常类型的完整 reached-path
PC。`OUTPUT_RELATION` 与 `TARGET_REACH` 不需要两套 branch planner、replay schema 或
validation；两者的区别仅是 bounded slice 和最终 reducer。branch flip 始终只是
`PathQuery -> ExecutionTask`，不是 ClosureGoal。

#### 原子迁移与删除顺序

1. **Region plan cutover**：Planner 对每个 `regionInstanceId` 只写一个 envelope，把现有
   producer/output demand 挂成 closure goals；Scheduler 只读新 schema 并编译 task。
   同一提交删除 `ACT.UPSTREAM.*` writer/reader、顶层 `captureGoal` 二选一和完整 row clone。
2. **Execution identity cutover**：runtime、instrumentation、raw result、Importer 和
   diagnostics 原子切到 `executionRef`；task-scoped token 成为唯一执行 identity。随后删除
   `activationId`/`sourceActivationId` 镜像和以 activation 为 execution scope 的 join。
3. **Path task cutover**：Worklist 直接从 SAT `PathQuery` 产生 compact task，删除
   `ReplayActivationFactory`、`ACT.PATH.*` 和旧 reachability bundle；path lineage 只保留
   `sourceTaskId/queryKey`。
4. **Explorer 收敛**：producer output 与 consumer target 共用一个
   `RegionClosureExplorer`，分别交给 output relation reducer 和 target reach reducer；删除
   `RegionCaptureGoal`、Scheduler 的 TARGET/OUTPUT 分支以及只服务旧 schema 的 shell 路径。
5. **清场**：全仓检查旧 activation prefix、capture-goal schema、兼容 adapter 和 fallback
   reader 已无生产消费者后直接删除；不保留双写、长期 dual-read 或 shadow validation。

每一步都只能增加直接替换旧实现的小型 record/codec，不建立通用 goal framework、event
bus、workflow engine 或第二套 proof hierarchy。同一不变量只在 Planner、Runtime、Importer
等真实 trust boundary 的拥有者处验证一次；内部 stage 传递 typed value，不反复
parse-and-prove。这是“不许过度设计、不过度验证”的具体执行规则，而不是放松 fail-closed。

每个 schema cutover 必须运行全部十三个真实 custom-JDK/Z3 fixture，保持：

```text
completed = 13
failures = 0
SAT/REACHABLE = 6
UNSAT/UNREACHABLE = 7
```

fixture 的 shared-field RPC、一次写/一次读、确定交互顺序和 workload 源码不得为迁移而改变。
额外快速回归只覆盖：一实例一 plan、goal slice/admission 互不泄漏、joint output 原子性、
同 goal 多 task 的 identity 隔离、单次 task 选择、旧 `ACT.UPSTREAM.*` /
`ACT.PATH.*` 不再出现；总量继续维持几十项，不锁定整份 JSON。

### 不可破坏的语义不变量

任何阶段只有同时满足下列不变量才可删除旧实现：

- 一个 output closure 只包含真实下游 demand 所需的 outputs。
- 每个 output 保留自己的 backward slice、capture/transformer proof 和 completeness；
  output B 的证据不能证明 output A。
- joint output 的所有 capture、PC 和 heap evidence 必须属于同一个原子
  `CONCOLIC_REGION_RESULT` row；row 的
  `(regionInstanceId, goalId, taskId)` 唯一确定执行身份。
- 任一 requested output 缺失、重复、无精确 binding 或不完整时，整个 joint summary
  fail closed；不能生成 partial relation。
- runtime read-from 继续要求 exact region instance、顺序以及适用的 object/value identity。
- worklist 只有在所有 output-relevant 可行 flip 已执行或证明不可行后才可 `CLOSED`。
- 正常但未写 demanded state 的路径必须具有 frame condition；异常退出不能伪装成普通
  output case。
- guarded relation 的每一个 case 都必须定义完整 demanded output set。
- Composer 只能绑定 relation 明确声明并由每个 case 提供的 output；偶然出现在
  `outputExpressions` 中的值不能升级为 producer port。
- unsupported expression、heap effect、binding 或 schema 必须成为显式 gap，不能 fallback
  成自由符号或可信结果。
- 当前输出继续停在 `CANDIDATE_ONLY`；本重构不实现自然 replay 的 trusted 升级。

### 当前结构问题

当前 workflow 本身是线性的，但内部 artifact 主要以 `JsonObject` /
`Map<String,Object>` 流动，导致每个阶段重复完成以下工作：

- 解析和规范化 method、cell、field、field path、port 和 site；
- 读取同一 JSON 字段并应用不同 fallback；
- 复制 output、slice、capture、method 和 completeness 镜像；
- 重建 graph index、backward/forward closure 和 canonical identity；
- 在 producer 与 consumer 两侧混合 schema 检查和语义证明；
- 为每个 CLI 重写 JSONL、hash、artifact 和错误输出；
- 在 solver 与 composer 中分别编码相同的 Java expression/SMT sort/operator。

结果是清晰的阶段图被少数万行级类中的协议搬运、兼容分支和重复验证掩盖。仅拆分类不会解决
这个问题；重构必须先改变内部数据模型和依赖方向。

### 目标数据流

内部 workflow 最终只流转类型化、不可变的 domain value：

```text
ProgramGraph
  -> RegionContract
  -> RegionInstancePlan
  -> ClosureGoal
  -> PathQuery
  -> ExecutionTask
  -> PathObservation
  -> RelationSummary
  -> RegionRelation
  -> CompositionQuery
  -> SmtProblem
```

JSON 只存在于入口、跨进程交接、持久化和调试导出边界。内部 stage 不直接从任意
`JsonObject` 猜测字段或 fallback；每种 wire schema 只允许一个 decoder/validator。

核心 value 类型包括：

- `MethodRef`、`CellRef`、`FieldRef`、`FieldPath`、`PortRef`、`SiteRef`；
- `StaticRegion`、`OutputSlice`、`OutputMember`、`OutputClosureContract`；
- `RegionInstancePlan`、`ClosureGoal`、`PathQuery`、`ExecutionTask`、`PathObservation`；
- `BranchWitness`、`BranchReplayContract`、`SolverPathContext`；
- `PathCase`、`RegionRelation`、`CompositionQuery`；
- `JavaExpr`、`SmtSort`、`SmtTerm`。

禁止引入通用 `Proof<T>` framework，也禁止再为同一事实同时维护多个 boolean 和 issues
镜像。阶段可以增加自己的运行证据，但不能重新解释上游已经验证过的静态语法。

### 目标模块与允许依赖

| 模块 | 唯一职责 | 目标生产行数 |
| --- | --- | ---: |
| `contract` | domain value、proof/gap、schema codec、canonical identity | 4–5k |
| `staticgraph` | immutable graph index、reachability、closure/path | 3–4k |
| `staticplan` | region boundary、input frontier、output slice、branch policy | 5–6k |
| `runtimeplan` | invocation/event index、read-from、runtime slice refinement | 4–5k |
| `executionplan` | definition/materialization/capture resolution、schedule | 4–5k |
| `instrumentation` / `runtime` | attestation、hook selection、execution evidence | 8–10k |
| `summary` / `campaign` | strict import、worklist、replay gate、guarded merge | 6–7k |
| `composition` | producer selection、relation emission、SMT、Z3 model codec | 8–9k |
| `artifact` / CLI | JSONL store、debug dump、config 和薄 orchestration | 3–4k |

依赖方向必须单向：

```text
contract <- staticgraph <- staticplan
contract <- runtimeplan
contract <- executionplan <- instrumentation/runtime
contract <- summary/campaign <- composition
artifact/CLI -> 各 stage 的公开接口
```

`runtimeplan` 可以用 runtime evidence 细化 `staticplan` 的 proof，但不能重新解析静态 graph
文本；Scheduler 只能把 validated goal/query 编译成 execution task；instrumentation 只验证
attestation 并选择 hook。

### Joint multi-output closure

`OUTPUT_RELATION` goal 使用独立、显式版本化的 `outputClosure` envelope。现有
`outputs[]` 只是可由 closure 编译出的 execution action，不再承担 demand schema；
static region、region plan、summary、worklist task 也不再靠同名 `outputs` 的形状猜测类型：

```json
{
  "outputClosure": {
    "schemaVersion": 1,
    "kind": "OUTPUT_CLOSURE_CONTRACT",
    "producer": {
      "regionId": "REGION.P",
      "regionInstanceId": "REGION.P@test#call7",
      "rootCallId": 7
    },
    "members": [{
      "output": {
        "portId": "REGION.P.out.0",
        "cell": "<P: int outX>",
        "kind": "SINK_STATE",
        "javaTypeDescriptor": "I",
        "selectionAuthority": "CONFIRMED_READ_FROM_EDGE"
      },
      "slice": {
        "inputPorts": ["REGION.P.in.0"],
        "sites": ["B_x"],
        "staticSites": ["B_x"],
        "methods": ["<P: void produce()>"],
        "causalEdgeIds": ["E_x"],
        "captureBindingsComplete": true,
        "captureBindings": [{
          "captureKind": "REGION_EXIT_FIELD",
          "captureBindingId": "REGION.P.out.0.exit-field",
          "outputPort": "REGION.P.out.0",
          "outputCell": "<P: int outX>",
          "accessRootInputPort": "REGION.P.in.1",
          "fieldPath": ["outX"],
          "fieldSignature": "<P: int outX>",
          "javaType": "int"
        }]
      }
    }, {
      "output": {
        "portId": "REGION.P.out.1",
        "cell": "<P: int outY>",
        "kind": "HEAP_STATE",
        "javaTypeDescriptor": "I",
        "selectionAuthority": "CONFIRMED_READ_FROM_EDGE"
      },
      "slice": {
        "inputPorts": ["REGION.P.in.0"],
        "sites": ["B_y"],
        "staticSites": ["B_y"],
        "methods": ["<P: void produce()>"],
        "causalEdgeIds": ["E_y"],
        "captureBindingsComplete": true,
        "captureBindings": [{
          "captureKind": "REGION_EXIT_FIELD",
          "captureBindingId": "REGION.P.out.1.exit-field",
          "outputPort": "REGION.P.out.1",
          "outputCell": "<P: int outY>",
          "accessRootInputPort": "REGION.P.in.2",
          "fieldPath": ["outY"],
          "fieldSignature": "<P: int outY>",
          "javaType": "int"
        }]
      }
    }]
  }
}
```

Envelope 不保存独立 `complete` boolean，也不复制 `capture` wrapper 或 execution
`location`；capture ledger 只存在于 member slice，execution action 从 output kind 编译。
decoder 只检查版本、wire shape、producer/member scope 与 ledger identity，任一 member
malformed 时整个 decode 失败，不能过滤坏 member 后返回一个较小的“完整”集合。动态
materialization/capture 正确性仍只由 Scheduler 与 Importer 在各自 trust boundary 证明。
完整 slice JSON 作为不可变 defensive copy 保留，因此 field owner、normal-exit field
path、transformer obligation 和 object identity 等证据不会在类型化过程中丢失。

每个 closure 派生两个不同身份：

- `DemandKey`：版本化、按 port 排序的
  `(portId, cell, outputKind, JVM descriptor)` 集合，只表示共同请求哪些 outputs；
- `closureFingerprint`：对每个 member 的完整 slice/capture contract 做 canonical hash。

真正的选择 scope 是
`(regionInstanceId, DemandKey, closureFingerprint)`。改变 output 集合会使 DemandKey
失效；集合不变但 proof 改变会使 fingerprint 失效，旧 worklist/manifest 不能误复用。

执行级 `symbolize`、`branches` 和 method admission 是所有 member slice 的确定性 union，
可在 schedule 中编译出来，但不是另一份语义 authority。原则是：

```text
union(member slices) 只驱动执行和探索；
member slice 单独证明对应 output。
```

Planner 先按一次 downstream demand（初版可以使用 downstream region instance，最终使用
composition demand id）收集同一 upstream instance 的 output port set，再按 canonical sorted
set 合并等价 demand。它不会预生成所有 output 子集，也不会把无关 consumer 的 outputs
无条件 union。

primitive field member 使用唯一逻辑 `REGION_EXIT_FIELD` capture；它覆盖 root method 的
所有正常 return，而不是绑定某个 writer。一次具体 replay 对每个 joint member产生一个最终
expression，任一 member 缺 capture、capture 重复或类型不支持时整个 joint goal fail
closed。Map/array/container 继续使用其 transformer contract，不能伪装成 scalar exit read。

删除目标：

- `requestedOutput`
- `requestedOutputSlice`
- `requestedOutputMethods`
- `requestedOutputCapture`
- `requestedOutputCaptureRequired`
- `requestedOutputCaptureComplete`
- singular-output planner/scheduler/importer/worklist/merger 分支
- output-closure 中把一个 root expression 自动复制给所有 outputs 的路径

迁移期间，旧 single-output artifact 曾由一个入口 adapter 转成 single-member contract，
只允许 dual-read、不允许 dual-write。当前所有 reader 已完成切换，adapter 已删除；
singular artifact 由 codec 直接 fail closed，不能再进入 operational path。

### Runtime 与 custom JDK 边界

custom JDK 保持稳定底座。现有 `startRegion`、symbolize、expression capture、
pause/resume PC、branch events 和 finish API 已能在同一次 region execution 中重复捕获多个
symbolic expressions。joint multi-output 不要求重写 VM、solver 或 HotSpot expression AST。

一个 raw-result row 本身就是一次 execution task 的原子结果；其中的 PC、heap evidence 和
全部 output captures 必须由同一个 task-scoped active token 产生，并由
`(regionInstanceId, goalId, taskId)` 绑定回唯一计划。Importer 逐 member 验证 capture
identity 和完整 demanded keyset，不再为每个 capture 复制执行身份。

只有跨线程共享一个 concolic context、跨进程 execution context 或原子 multi-heap snapshot
才可能需要较大 custom JDK 修改；这些不属于当前 joint-output scope。

### JSON、artifact 与调试

本轮保留跨进程所需的 JSONL artifact、failure diagnostics 和 `run_engine.sh --debug`
投影，但没有为它们建立第二套 domain model。统一 `ArtifactStore` 是长期 `DEFERRED`
目标；如果未来能实际替换重复 I/O，它才应提供：

- `OFF`：成功路径不写中间调试数据；
- `SUMMARY`：写 id、状态、计数和 diagnostics；
- `FULL`：写完整 stage input/output/evidence；
- 任意失败自动写可 replay 的 failure bundle。

届时所有 artifact 应使用同一个 canonical codec，调试 identity 至少包括 `campaignId`、
`demandKey`、`regionInstanceId`、`goalId`、`queryKey`、`taskId` 和 `summaryId`；一次
runtime row 直接由 `taskId` 定位，不再用 activation 加 content hash 模拟 execution
identity。长期目标 CLI 是：

```text
inspect <artifact>
explain <diagnostic-id>
diff <artifact-a> <artifact-b>
trace <task-id-or-query-key>
replay <failure-bundle>
```

当前跨进程所需的 execution evidence、summary/relation 和 terminal candidate 继续持久化；
现有 debug formatter 直接读取这些 artifact。`OFF/SUMMARY/FULL` policy、统一 failure
bundle 和上述 inspect CLI 尚未实现，不把它们计作本轮完成项。

### 迁移阶段

当前实施状态（2026-07-24）：

- Phase 0 `COMPLETED`：配置指定的 custom JDK 已完整构建；十三个 maintained workload
  已经执行真实 concolic campaign 和真实 Z3，结果为六个 `sat`、七个 `unsat`，没有 skip。
  矩阵使用一次 Maven 构建和十三个隔离 workdir 并行执行，shared JAR 在执行前后由 SHA-256
  校验为未改变。
- joint-output vertical slice `COMPLETED`：`OutputClosureContract` 已成为唯一 writer；
  Planner 按 producer invocation 与 downstream demand 生成 canonical member set，
  Scheduler/Runtime/Importer 在一个原子 result row 中处理全部 captures，Worklist/Merger
  使用 demand/fingerprint identity，Composer 按 exact output set 选择一个 relation，并让
  全部 outputs 共享 case selector。shell campaign 同样按 demand identity 去重，不再按
  output channel 重复执行同一个 producer。
- Phase 1 的 accepted scope `COMPLETED`：canonical rendering/hash helper 和唯一
  output-closure codec 已替换对应的重复 JSON 逻辑。全仓铺设
  `MethodRef/CellRef/FieldRef/FieldPath` 类型体系 `DEFERRED`；在没有可立即删除代码的
  场景下，它会成为与现有 workflow 平行的 framework。
- Phase 2 `COMPLETED`：Java 与 shell 的 operational reader/writer 都只接受
  `outputClosure`；Importer 直接消费 typed member 和 execution-scope union，内部 singular
  member view、`requestedOutput*` dual-read/dual-write 和 shell fallback 已删除。codec
  中保留的 singular 名称只用于 fail-closed 拒绝旧 artifact。
- Phase 3 的 accepted scope `COMPLETED`：finalized static edge rows 由保序、保重复的
  `StaticGraphIndex` 统一提供 method/incoming/outgoing/id view，替换
  `SymbolicRegionPlanner` 中重复的全图扫描。把 boundary/input/output planner 物理拆类及
  把 facade 做薄 `DEFERRED`；当前没有证据表明单纯搬代码能降低语义或代码负担。
- Phase 4 的 accepted scope `COMPLETED`：同一 producer invocation 与 canonical output
  demand 只生成一个 activation，Scheduler 逐 member 编译 capture，Runtime 继续使用一个
  ActiveRegion row。旧 instance row、activation/ConcreteDemandSlice 派生镜像、retired
  selector 和零引用 active-region API 已删除。invocation/event/read-from 物理拆类
  `DEFERRED`，除非以后能同时删除重复实现。
- Phase 5 `COMPLETED`：Importer 逐 member fail closed，producer attestation 与 importer
  verification 仍是两个真实 trust boundary；固定 four-put / ordered-put 双射已删除。
  schema-v1 container mutation 现在按 declaration 的 selector、finite-array snapshot、
  dynamic consumer 和 exact transformer obligation 逐项证明，数量、稀疏 index、raw
  load 邻接与排序都不再是语义条件；同一 static base 的多个 occurrence 在 Composer 中
  保持各自的 dynamic term。
- Phase 6 的 accepted scope `COMPLETED`：worklist、merge、composition 都使用 exact
  demand/fingerprint，所有 demanded outputs 共享一个 case selector。共享 primitive
  Java-expression-to-SMT core `REJECTED`：完整试验最多净减 112 行，却新增约 376 行抽象；
  试验发现的 `ConSymbolExp` 常量分类错误已用两处局部修复解决。把 shell campaign 搬成
  Java `ExplorationCampaign` `DEFERRED`；现有 shell 负责真实进程边界，尚无正确性缺口或
  净简化证据。
- Phase 7 的 accepted scope `COMPLETED`：普通回归已从 39 类 / 724 项压缩为
  13 类 / 57 项且全部通过；
  一次明确授权的 `cross-method-fields` 重构把 Producer A 从 110 cases / 109 replays 缩成
  4 cases / 3 replays，并新增同一 invocation 的 `a/aWitness` 联合输出、完整 case keyset 和
  shared-selector 真正端到端门禁；最终 truth table 不变且真实 Z3 为 `sat`，本机完整耗时由
  约 61 分钟降到 2 分 49 秒。生产 Java 当前为 81,084 行；相对 84,166 行阶段起点累计
  净减 3,082 行，也比 81,594 行冻结基线少 510 行。除上述 authority cutover 外，已删除
  Replay 派生布尔/计数镜像、Composer 三个零消费者 catalog、Importer 纯 dead helper，
  同时保留原始 failure codes、SMT assertion 和 summary hash。
- 并行后的 robustness follow-up `COMPLETED`：增强后的 `unreachable-parity` 在不改变
  single-publish/single-read shared-field RPC 的前提下加入两个 nested int leaf、clamp、
  short-circuit 与后置分支；修复 static binding-id collision、Boolean-only snapshot
  import 和 read-only Map 单字段假设。serial/40-worker 分别闭合相同的 12/14 条 producer
  paths，四个 Boolean valuation 均由 Z3 判定 `unsat`。concrete observation 现在只由相同
  `closure + site + occurrence` 的 symbolic EXPLORE witness 覆盖，失败 wave 会打印并保留
  exact task artifact。
- scalar/object UNSAT follow-up `COMPLETED`：新增 correlated joint fields、nested plain
  object fields 和 inherited same-object alias 三个 fixture。三者都保持 deterministic
  single-write/single-read shared-field RPC，四个 Boolean valuation 均由真实 Z3 判定
  `unsat`。其中 correlated producer 的两个 output 在一次 activation 和每个 merged case
  中共同出现，直接覆盖 multi-output 相关性；runtime shell 先排除
  `symbolicReady=false` activation 再解析其 closure，避免一个明确不可执行的重复候选阻断
  同 region 的有效 producer demand。
- additional field-root follow-up `COMPLETED`：新增 irrelevant post-snapshot object
  mutation 与 nested long-field parity 两个 fixture。前者证明后续无关 heap write 不进入
  requested output closure，后者把 `J` descriptor、跨 helper field propagation 和 disjoint
  long output images 纳入真实 Z3 `unsat` 门禁；两者仍保持确定性 single-write/single-read RPC。
- compound target follow-up `COMPLETED`：target exception 不再只消费一个 directed
  branch query；静态 seed 纳入 target method 中任一 successor 可到精确 throw 的 branch，
  target worklist 闭合普通/异常路径，Composer 对精确异常 summary 的完整 PC 取 OR。新增
  reachable/unreachable 两个 deterministic shared-field fixture 覆盖前置 guard、
  nested object/多变量传播以及 AND/OR 短路。
- correctness follow-up 后的低风险清理 `COMPLETED`：删除零引用 private helper/constant，
  将三份相同的 JVM descriptor 规范化收敛到既有 primitive semantics authority，并合并
  if/switch 的 exact marker prefix 与 symbolic/concrete 的公共 runtime result 构造。没有
  新增兼容层、schema 或 custom-JDK 分支；边界校验仍留在原 trust boundary。
- 最终源码已从构建、静态分析、runtime planning、完整 target/producer campaign、
  merge/composition 一直执行到真实 Z3；十三个隔离 workload 全并行完成，结果为六个
  `sat/reachable`、七个 `unsat/unreachable`，0 failure，没有用旧 artifact 或增量
  re-compose 代替门禁。custom JDK/`third_party` 未修改。
- 全量 typed internal pipeline、`ArtifactStore`/inspect CLI、planner 大拆类以及
  45,000–55,000 行宏观目标统一标记为长期 `DEFERRED`，不是本轮正确性里程碑。实测没有
  净简化收益的重写不会为了“完成阶段”而强行加入；若未来重新启动，仍须遵守本节的
  trust-boundary 与十三-fixture 门禁。

#### Phase 0：冻结行为与端到端基线

- 记录十三个 maintained workload 的 candidate reachability 和直接 Z3 结果。
- 保存 normalized root-input catalog、truth table、relation case counts 和 terminal manifest。
- 建立 semantic diff：比较 SAT/UNSAT、root sorts、producer bindings 和 relation cases，
  不要求 JSON 字节、summary id 或非语义字段完全相同。
- custom JDK 未构建或矩阵未完成时，本阶段只能是 `IN_PROGRESS`。

#### Phase 1：共享无语义策略的基础设施

- `COMPLETED`：在实际 output/replay boundary 统一 canonical JSON、hash 和只读 adapter。
- `DEFERRED`：全局 `MethodRef/CellRef/FieldRef/FieldPath` parser/type hierarchy；只有能立即
  删除重复 parser 时才局部引入。
- 对 producer/consumer trust boundary 保留独立语义验证。
- 首批只替换 replay validation 中与现有算法完全等价的 canonical rendering，不改
  worklist/query/summary identity。

#### Phase 2：类型化 contract 与唯一 codec boundary

- `COMPLETED`：`OutputClosureContract` 和 codec 取代 singular output wire schema；
  single output 只是
  canonical member set 的一个元素。
- 只在一种类型能立即删除重复 parser、identity 或 completeness 代码时引入它；不建立通用
  `Proof<T>`、第二套 artifact model 或与现有 workflow 平行的 framework。
- 所有 wire reader 只消费 canonical `outputClosure`；逐成员复用只能通过 codec 的唯一
  internal view，禁止在 consumer 中直接实现 `requestedOutput*` fallback。
- Importer 完成 joint-native 提取后删除 internal member view，不永久保留迁移层。

#### Phase 3：静态 graph 与 planning

- 保留 `SeedBackwardStaticAnalyzer` 的可变 Soot CFG、relevance worklist 和全程序
  writer/callsite 索引；它与 finalized edge graph 的停止条件和副作用不同，不能塞进一个
  通用 `GraphClosure`。
- `COMPLETED`：只在 edge rows 补全 `transferKind/siteId` 之后，为
  `SymbolicRegionPlanner` 构建一个
  保序、保重复 edge 的 immutable `StaticGraphIndex`，替换 Planner 内部重复的 method、
  incoming/outgoing 与 edge-id 扫描；它不拥有 heap/container 语义或查询 DSL。
- `DEFERRED`：将 boundary、input frontier、output slice、branch policy 物理拆成独立
  planner，并把 `SymbolicRegionPlanner` 做成薄 facade；没有净删除证据时不做搬家式重构。
- `COMPLETED`：先独立计算每个 output member slice，再构造 joint execution union。

#### Phase 4：runtime planning、schedule 与 instrumentation

- `DEFERRED`：将 invocation/event/read-from index 物理拆出 `RuntimeRegionPlanner`；只有能
  删除重复状态而不只是换文件时再实施。
- `COMPLETED`：一个 upstream invocation + canonical demanded output set 产生一个
  activation。
- `COMPLETED`：Scheduler 逐 member 选择唯一 capture；任一 member 失败则整组不调度。
- `COMPLETED`：Instrumentation 消费 canonical schedule 和 attestation，复用现有
  call/field hooks。

#### Phase 5：runtime evidence 与 strict import

- Runtime 以一个 ActiveRegion result row 作为原子 execution envelope，并输出 typed
  capture rows；不为同一 row 重复增加 `executionId`。
- Importer 先逐 member 提取一次 output，再把 validated extraction 交给 heap verifier。
- 删除 global exact-capture mode、root-output broadcast、重复 output extraction 和对
  capture plan 的重复扫描。
- `COMPLETED`：删除 `exactOrderedPutBijection` 中“数组长度 4 / 四次 Map.put”的
  workload-shaped 特例，改为与长度、selector 密度和 event 邻接无关的逐 declaration
  finite-selector/effect/transformer 证明；没有保留 fixture 常量或新增旁路。
- runtime producer attestation 与 importer consumer verification继续独立。

#### Phase 6：campaign、merge、composition 与 SMT

- `COMPLETED`：Worklist identity 改为 canonical output demand；complete-empty slice
  表示零 relevant
  branch，而不是 wildcard。
- `COMPLETED`：Merger 按 exact producer invocation + demand 分组，每个 case 验证全部
  outputs。
- `COMPLETED`：Composer 复用 multi-output map 和 shared case selector，只绑定 declared
  outputs。
- `REJECTED`：让 `ConcolicConstraintSolver` 和 `ConcolicSmtComposer` 共享完整
  Java-expression-to-SMT core。实作试验新增的抽象显著多于净删除；继续保留原边界，只保留
  试验发现的局部 correctness 修复。原抽取边界是
  只合并 primitive cast、数值/比较、基础 String、sort/term 与 precondition 传播；各自保留
  symbol resolution、placeholder policy、array/Map、model materialization 与
  relation/heap emission。一旦共享需要模式开关或大量 callback 就停止抽取。
- `DEFERRED`：把 shell exploration 状态机迁入 Java `ExplorationCampaign`；当前 shell
  本身就在负责进程边界，尚无替换收益。

#### Phase 7：切换与删除

- `REJECTED`：长期保留新旧 writer 做 shadow-run；这会违反唯一 authority。改用冻结
  semantic baseline、boundary regression 和十三-fixture 真实 Z3 matrix。
- `COMPLETED`：每个 authority 切换后运行 full maintained matrix，再删除旧 schema、
  fallback、mirror、private parser 和兼容 shell reader。
- `COMPLETED`：所有 operational reader 已切换到 schema-v1 `outputClosure`，旧 artifact
  由 codec fail closed；没有保留 v1 dual-read adapter。
- `COMPLETED`：重新统计净生产行数，只有实际删除后的代码计入上述结果。

### 正确性与回归门

普通单测用于快速定位，但重构的 release gate 是实际 workload 和真实 Z3：

```bash
# 精简后的 57 个 boundary regression（包含真实 Z3）
mvn -q test

# 三个核心三线程 workload
experiments/generic/three-thread-rpc/run_robustness_matrix.sh core

# 全部十三个 maintained workload
experiments/generic/three-thread-rpc/run_robustness_matrix.sh all

# 推荐：只构建一次，十三个 workload 使用隔离目录和日志全部并行
experiments/generic/three-thread-rpc/run_robustness_matrix_parallel.sh all
```

完整矩阵的预期顶层结论固定为：

| Profile | Candidate | 直接 Z3 |
| --- | --- | --- |
| `baseline` | `REACHABLE` | `sat` |
| `cross-method-fields` | `REACHABLE` | `sat` |
| `multitype` | `REACHABLE` | `sat` |
| `dependent-scalar` | `REACHABLE` | `sat` |
| `containers` | `REACHABLE` | `sat` |
| `unreachable-parity` | `UNREACHABLE` | `unsat` |
| `unreachable-correlated-fields` | `UNREACHABLE` | `unsat` |
| `unreachable-nested-object` | `UNREACHABLE` | `unsat` |
| `unreachable-inherited-alias` | `UNREACHABLE` | `unsat` |
| `unreachable-mutated-object` | `UNREACHABLE` | `unsat` |
| `unreachable-long-fields` | `UNREACHABLE` | `unsat` |
| `compound-target` | `REACHABLE` | `sat` |
| `unreachable-compound-target` | `UNREACHABLE` | `unsat` |

fixture main 和普通 fixture JUnit 只验证 concrete workload，不是 SMT gate；
`experiments/generic/test_workflow.sh` 使用 dry-run/fake Z3，也不能替代上述矩阵。

### 回归测试精简目标

2026-07-23 的普通 JUnit 基线是 39 个 `*Test` 类、724 个可执行测试方法；其中六个巨型
测试类占 479 项。这个规模主要在重复锁定 JSON 字段、private helper 和同一路径的类型排列，
并没有形成 724 个独立的语义保证。当前已经压缩为 13 类、57 个可执行测试，`mvn -q test`
全部通过。

普通 suite 固定维持约 40–60 个高价值测试，按 boundary 组织而不是按实现分支堆叠：

- contract/codec、static planning、runtime planning、schedule、runtime capture、import、
  worklist、merge、composition 各保留一个小型测试类；
- 每个 boundary 通常只保留 happy path、malformed/untrusted、identity/ambiguity、
  completeness/empty 和 joint atomicity；
- 两处 Java/SMT lowering 各自使用少量表驱动测试覆盖 integral、String/null、FP 和
  unsupported fail-closed；
- 删除七个仅重复执行 workload main 的 fixture JUnit，但绝不删除或改动十三个 maintained
  workload main、配置和实际 Z3 matrix；
- 每批合并或删测前后都运行十三个 fixture，一直保持六个 `sat`、七个 `unsat`。

普通测试的可复现计数命令是：

```bash
rg -g '*.java' '@Test\b' src/test | wc -l
```

每一阶段的退出条件：

1. 涉及的快速真实 Z3 门无 skip 且通过；
2. `run_robustness_matrix.sh core` 通过；
3. 删除旧实现前 `run_robustness_matrix.sh all` 通过；
4. 新旧 semantic diff 没有 root sort、binding、case 或 SAT/UNSAT 漂移；
5. unsupported/gap 不少于旧实现，不能因为 fallback 获得更多“成功”；
6. custom JDK 与 Z3 环境缺失时不允许声称阶段完成。

### 回滚、兼容与提交纪律

- 一次只切换一个 stage authority；每个阶段都能独立回滚。
- 迁移 adapter 集中在 contract/codec 层，禁止每个 consumer 自写兼容分支。
- 允许短期 dual-read，禁止 dual-write 和两个 completeness authority。
- artifact schema 改变时必须 bump version，并使旧 worklist/cache/query identity 失效。
- identity/hash 改动必须先有 golden semantic identity 测试，再触及 worklist、summary id 或
  composition binding。
- canonical cleanup 不改变 custom JDK、SMT emitter 或 terminal manifest；identity 的变化
  只允许来自 canonical output demand，并由 worklist/merge/composition boundary test 与十一
  fixture 的真实 Z3 结果共同证明。

### 完成定义

本轮 joint-output authority cutover 与 correctness-preserving cleanup 完成必须同时满足：

- 十三个 maintained workload 保持上述六个 `sat` 和七个 `unsat`；
- single-output 是 multi-output contract 的单 member 情况，不再有独立运行路径；
- Java 与 shell operational path 只读写 canonical `outputClosure`，旧 singular 字段只能在
  codec 的拒绝列表和迁移说明中出现；
- demand identity、member capture proof 和 completeness 各只有一个 authority；
- runtime/importer 的独立 trust-boundary 验证仍然存在；
- 被新 authority 替代的旧 schema、mirror、fallback 和 adapter 已删除；
- custom JDK 不因本重构承担新的核心算法；
- 普通回归维持几十项且全部通过，最终 production LOC 和相对基线差异被明确记录；
- 每个重要 milestone 独立 commit/push，最终工作树与 `origin/main` 同步。

全量 typed internal pipeline、JSON 只在 artifact 边界、统一 `ArtifactStore` CLI 和
45,000–55,000 行目标属于长期架构方向，不再伪装成本轮完成条件。它们只有在能替换现有
代码、关闭具体正确性缺口并通过同一十三-fixture 门禁时才重新进入实施计划；单纯拆文件、
搬 JSON 或增加 wrapper 不算进展。

## 下一轮大规模精简计划：61k–69k

第一轮合理目标是净减 12,000–20,000 行，把当前 81,581 行手写生产 Java 降到约
61,000–69,000 行。45,000–55,000 行仍是长期目标，但不能靠删除证明字段、削弱
fail-closed、把代码搬家、压缩格式或生成代码凑数。

本轮最高原则仍是：

1. 正确性优先，全部 maintained fixture 的真实 concolic/Z3 语义不能改变；
2. 不过度验证：同一事实只在真实 trust boundary 验证一次；
3. 不过度设计：新 abstraction 必须立即替换并删除旧实现；
4. 行数是删除重复 authority 后的结果，不是独立 KPI。

计划中的字段与类名都是删除候选，不是预先批准的删除清单。每项必须先由 field ledger
确认 writer、Java 生产 reader、shell reader 和语义用途；发现真实消费者或 correctness
authority 时，更新 ledger 并保留，而不是为了完成 PR 强删。

### 删除原则

字段分为三类：

- 零生产消费者、协议常量、纯计数镜像：直接删除；
- 当前有消费者，但可由唯一 canonical object 无歧义推导：原子 schema 升级后删除；
- 参与 fail-closed、运行时身份、read-from、output closure 或异常路径闭包的证据：必须保留。

所有 schema 迁移采用一次性切换：writer、Java reader、shell reader 在同一个 PR 更新，
旧 artifact 直接拒绝；不保留双写、长期 fallback 或 shadow schema。

这是全新版本重构，不提供旧 artifact 向新 schema 的迁移承诺。新 authority 切换后，旧
reader、旧 writer、兼容 adapter、legacy parser、fallback 分支和只服务旧格式的测试必须在
同一个 PR 删除；不能以“以后再清理”为理由留在主路径。

### PR 0：冻结语义基线

先记录：

- 当前 81,581 行生产代码；
- 全部十三个 workload 的 SAT/UNSAT、relation case 数、trace/artifact 大小和各阶段耗时；
- 一份一次性 field ledger：字段、writer、生产 reader、shell reader、是否可推导、删除 PR；
- 测试只检查语义 contract 和 retired field 不再出现，不锁定整份 JSON 字节形状。

这一步不改变系统行为。基线和 ledger 是删除决策的工作文件，不演化成第二套长期 schema。

### PR 1：删除确定的死代码和死字段

#### 静态分析链

从 `CausynthAnalysisResult` 核查并删除无生产消费者的：

- `seeds`
- `cells`
- `symbolicModels`
- `automaticDerivationBoundary`
- 最终整个 `slices`

连带候选：

- `collectCells()`、`cellKind()`
- `buildAutomaticDerivationBoundary()`
- 从未填充的 `modelSummaries`
- `candidateRelation`
- branch policy 的 `sourceEdgeIds`
- `requiredModels -> models` 整条无执行消费者链
- 所有只写入 `result.slices` 的统计量

`instrumentConcolicRegions()` 改为返回小型 typed `InstrumentationResult`，只覆盖当前真实
局部读取，随后删除万能 `Map slices`。

#### Scheduler 和 runtime

核查并删除 `ConcolicScheduler.Result.jobs` 镜像及 `JsonObject job` 林造，改用
`scheduledPrimaryCount` 控制配额。连带候选：

- `Result.mergePlan`
- `Candidate.reason`
- `workloadKind()`
- job 中第二份 `materializations`、`edgeBindings`
- `selectionReason`、`captureReady` 等 job-only 字段

从 raw concolic result 核查并删除无消费者的：

- `runtimeThread`
- `runtimeThreadId`
- `concretePrimitiveOutput`
- `durationNanos`
- `test`
- `invocationOrdinal`
- `branchReplayValidation`

Scheduler binding 候选：

- 固定 `objectIdentityRequired=false`
- `discoveredExecutionId`
- `discoveredExecutionIds`

#### Worklist、Composer

核查并删除：

- `ConcolicSmtComposer.MergeStats`
- worklist task 的固定 `status=PENDING_SOLVE`
- `dynamicIdsExcludedFromQueryKey`
- 可由 closure/activation 推导的 `rootMethod`
- 顶层 `regionInstanceId/rootCallId/outputDemandKey/outputClosureFingerprint` 镜像
- 无消费者的顶层 `engineArrayInputBindings`
- `caseProjectionCatalogComplete`
- relationship 的固定 `status=UNVERIFIED_CANDIDATE`

独立 `RegionSummaryMerger` 已删除；relation 只由 Worklist 在
`CLOSED + OUTPUT_RELATION_CLOSURE` 转移中产生。原 Merger 中可由 canonical 数组、
`gaps`、`kind/schema` 推导的下列镜像也不再存在：

- `caseCount`
- `guardSemantics`
- `mergeSemantics`
- `coverageSemantics`
- 固定 authority
- manifest 的 `diagnosticCount/status/semanticAuthority/domainSemanticAdapterAllowed`

### PR 2：压缩静态分析模型和 artifact

当前 Planner 先生成 rich `Map`，随后 `StaticRegionArtifactSchema` 深复制并删除大量字段。
改成：

1. 用精简 `MethodFacts` 替代 `SymbolicExecutionPlanBuilder` 的大 Map；
2. `MethodFacts` 只保留 `method/classification/symbolicInputs/outputs/siteIds`；
3. 核查并删除 Builder 中的：
   `id/requiresSymbolicExecution/reason/edgeCount/heapInputs/environmentInputs/guards/`
   `exceptions/transferKinds/possibleCallees/runtimeObservedCallees/truncated/precision`；
4. 扩展 `StaticGraphIndex` 后删除已被替代的 `SymbolicPlanningStage` 和
   `SymbolicExecutionPlanBuilder`；
5. Planner 直接构造 canonical `StaticRegionArtifact`，删除 deep-copy-then-strip；
6. output slice 不同时携带 `causalEdges` 与 `causalEdgeIds`，只通过 ID 查 canonical edge
   table。

`target_resolved.json` 保留，但压缩为最小 target attestation：

- schema/kind
- target id
- method
- exception
- construction ordinal
- analysis scope

候选删除 `seedMode`、重复 `seedException`、恒等于 1 的 count、singleton method list 和
纯诊断变量列表，并在同一个 PR 同步 Java/shell readers。

截至 2026-07-25，PR 0、PR 1 已完成，PR 1 的隔离全矩阵为 13/13、6 SAT/7 UNSAT。
PR 2 已完成实现：method plan rich Map 两个类已经删除，region planner 只保留五字段
`MethodFacts`；static region 直接产生 canonical row，output slice 只存 canonical edge
ID；target attestation 已一次性切到 V2。该里程碑已通过快速回归以及 baseline、
dependent-scalar 的完整 concolic/worklist/merge/compose/Z3 流程。用户工作树中的
container fixture 修改不属于重构提交，也不会被覆盖或暂存。

### PR 3：静态 edge 和 runtime activation schema V2

#### Static edge

将：

- `mappingOnly`
- `semanticAssertionsAllowed`
- `eligibleForAutomaticDerivation`
- `eligibleForAutomaticSmt`
- 固定 `direction=backward_provenance`

收敛为：

```json
{"semanticMode":"ASSERTABLE | MAPPING_ONLY | RUNTIME_VALIDATION_REQUIRED"}
```

decoder 根据枚举检查对应必要字段，不再维护相互可能冲突的布尔组合。

#### Runtime activation

将 readiness 收敛为：

```json
{
  "admission": {
    "state": "EXECUTABLE",
    "mode": "RUNTIME_ROOT_REPLAY",
    "blockers": []
  }
}
```

它替代：

- `replayable`
- `boundaryReady`
- `symbolicReady`
- `schedulerReady`
- `runtimePathEvidenceComplete`
- 各种 truncation boolean
- `runtimeGaps`
- `replayMode`

root 选择字段压缩为 tagged `rootSelector`，bundle 字段压缩为一个 `bundle` 对象。

Edge evidence 改为 discriminated schema，例如：

```json
{
  "evidenceKind": "COMPLETE_VALUE_EQUALITY_V1",
  "fingerprint": "...",
  "writerEventSeq": 10,
  "readerEventSeq": 20
}
```

删除 `relation/relationKind`、endpoint sequence aliases、固定 authority 与
`confirmed=true` 镜像。runtime planner 必须提供 static graph，同时删除
`catalogSupplied=false`、`legacyStatic()` 等 graphless 兼容路径。

截至 2026-07-25，PR 3 的第一个原子切换已经完成：static dataflow edge 与 static
region 统一升到 V2，五个互相镜像的 edge policy 字段已由唯一 `semanticMode` 替代；
runtime discovery、scheduler、instrumentation 与 runtime executor 的九个 readiness/
replay/truncation 字段已由唯一 `admission {state,mode,blockers}` 替代。旧字段没有双写、
fallback 或兼容 reader。57 项快速回归全部通过，baseline 的 target 与两个 producer
path campaign、summary merge、SMT composition 和 Z3 端到端结果仍为 `sat`。回归还发现
并修正了 Scheduler 遗留的 static graph V1 authority 常量；否则 V2 图会被错误降级并使
producer activation 阻塞。第二个原子切换将七个顶层 activation bundle 镜像压缩为唯一
`bundle {rootActivationId,scheduleId,role,index,size,selection}`，同步切换 Java 与 shell
reader，无双写；57 项快速回归与 baseline 端到端 Z3 仍通过。PR 3 剩余的
root selection 也已一次性收敛成 tagged
`rootSelector {kind,method,receiverClass?,thread?,ordinal,arguments?}`：删除顶层
`rootMethod/receiverType/invocationOrdinal`、context authority/boolean 镜像和 argument
selector schema/authority 镜像，不保留 legacy/global fallback。迁移回归发现并修正了
worklist identity 的旧顶层 root 读点；57 项快速回归和 baseline 全流程仍通过。PR 3
同时删除 runtime planner 的 graphless overload、`catalogSupplied=false` 和
`legacyStatic()` 宽泛输入路径；所有 planning 现在必须消费同一份 frozen static graph，
57 项快速回归和 baseline 全流程仍通过。最后一个原子切换将 runtime edge binding
统一成三种 discriminated evidence：
`COMPLETE_VALUE_EQUALITY_V1`、`FIELD_ASSIGNMENT_READ_FROM_V1` 和
`CONTAINER_MUTATION_READ_FROM_V1`。writer、Scheduler、Composer 与回归 fixture
一次性切换到 `evidenceKind + writerEventSeq + readerEventSeq + kind-specific payload`；
已删除 `relation/relationKind`、sequence aliases、`confirmed` boolean、固定 authority、
path-completeness 镜像和只写不读的 write-evidence wrapper 字段。证据种类本身决定
必需 payload，reader 不猜旧字段，也不保留兼容 fallback。57 项快速回归通过；完整
13-fixture matrix 是该 PR 合入前的最终 gate。

### PR 4：压缩 trace、Importer 和 replay admission

默认 trace 只写 Planner 真正读取的字段。候选删除：

- `timeNanos`
- 重复的 `test/process/threadName/tid`
- execution event 的 `parentCallId/unitIndex/declaredType/expression/exceptionType`
- `hasOutcome + outcome` 双字段，改为可选 `outcome`
- `hasSuccessorIndex + successorIndex` 双字段，改为可选值

Importer 收敛为：

- raw row 只 decode 一次；
- 建 capture、binding、observation、site/occurrence、model symbol 索引；
- `(activationId, regionId, regionInstanceId)` 使用严格唯一索引，禁止静默覆盖；
- summary ID 只 hash canonical semantic payload，不 hash 无关诊断字段；
- replay 的唯一校验迁入一个 `ReplayAdmission`；
- 删除重复 branch validation。

确认 unique checks 已迁移后删除 standalone gate；保留小而独立的
`BranchReplayObservationValidator`，以及 Map.Entry/container fresh rebinding
所需的最小 model admission。

截至 2026-07-25，PR 4 的 trace V2 原子切换已开始：每行明确携带
`schemaVersion=2`，offline aggregator 直接拒绝旧行；全局 `seq` 已取代未消费的
`timeNanos`，`outcome/successorIndex` 改为真正的可选字段。execution row 删除了未进入
Planner 的 test/process/thread、parent/unit/type/expression/exception 镜像，field row
删除同样未消费的 run/thread 镜像，METHOD_ENTER 仍保留调用树、线程和 receiver
identity。Importer 的 activation/region 索引不再静默覆盖重复 key，path replay 也删除
了 standalone `ConcolicPathReplayVerifier`；Importer 是唯一 admission 调用点，shell
只检查单行 artifact identity 并生成最小 exploration record。原 `ConcolicReplayValidator`
中并非重复的 Map.Entry、array/container 跨执行 fresh-identity rebinding 证明继续保留，
不能为了减行误删。切换过程中 fixture 及时发现 robustness shell
仍读取 PR 3 的旧 `relation/orderConfirmed/selectionAuthority`；Java 产物本身正确，
shell reader 已同步改为三种 `evidenceKind` 的最小 payload 检查，未增加 fallback。
当前 `dependent-scalar` 已覆盖 target path flip、两个并行 producer campaign、8 个
guarded cases 与最终 Z3 `sat`；131 行 runtime trace 全部是 V2，retired trace 字段零出现。

### PR 5：Worklist、merge 和大 SMT schema 收敛

- `outputClosure` 是唯一 closure carrier，删除顶层 producer/demand 镜像；
- 保留 `demandKey` 和 `closureFingerprint` 各自语义，不能误合并；
- `regionRelation.complete`、case/summary `relationallyComplete` 收敛成顶层唯一 gate；
- merged summary 删除 `activationId=MERGED_PATHS`、producer identity 镜像和
  `sourceRegionInstanceIds`；
- case 使用完整 path hash 作为 `caseId`，删除重复 `pathKey`，运行时派生 `symbolScope`；
- 四套 gap 集合合并为 `gaps:[{kind,subject}]`，唯一准入条件是 `gaps.isEmpty()`；
- `resolvedEdgeBindings` 只存 binding/edge ID，不复制完整 binding；
- artifact ref 删除 `sizeBytes`，保留 `path + sha256`；
- Boolean report 收敛为 `roots + valuations + reachCondition`，删除重复 truth-row 派生字段。

截至 2026-07-25，PR 5 已完成实现并进入全矩阵验收。worklist manifest 现在直接携带
canonical `outputClosure`，不再镜像 `outputDemandKey/outputClosureFingerprint`；
Merger 以该 contract 校验同一 bounded demand。merged summary 只保留一个顶层
`relationallyComplete`，case ID 使用完整 path hash，case scope 在 Composer 内派生。
Composer manifest 的四套缺口已统一为 `gaps:[{kind,subject}]`，case coverage 和 fatal
query readiness 也进入同一 gap gate；`resolvedEdgeBindings` 只存 canonical edge ID。
artifact binding 只保留 `path + sha256`。Boolean report V3 只保留
`roots + valuations + reachCondition + gaps`，SAT/UNSAT 由 valuation `status` 唯一表达，
不再双写 `reachesBug/valuationKey/solverStatus`。Importer 的 summary ID 只 hash
canonical semantic payload。57 项快速回归、generic workflow shell test 和
`dependent-scalar` 的双 producer/8-case/Z3 端到端均已通过（`REACHABLE/sat`）。

### PR 6：替换高复杂度算法

#### 静态 worklist

把 `SeedBackwardStaticAnalyzer` 的 bounded full scan 改为 dirty queue：

- 新 method 才进入 method queue；
- 新 state 才重新处理对应 method；
- caller/field-writer/constructor expansion 每个 key 只执行一次；
- projected propagation 只处理新增 edge。

#### Runtime planning

一次建立：

```text
callId -> invocation
parentCallId -> children
callId -> runtime/field events
(test, method) -> ordered invocations
(field, receiverObjectId) -> ordered reads/writes
digest -> ordered endpoints
invocationId -> completion
```

随后：

- root activation 只遍历自己的 subtree；
- latest writer 用 binary search；
- 删除 upstream×downstream、write×read 的笛卡尔积扫描；
- HDFS 循环场景主要查询从二次/三次扫描降到近似 `O(E log E)`。

#### Composer

- 预建 `SummaryIndex`，用 monotone demand queue 替代反复整图 pass；
- equality fixed-point 改为 union-find；
- causal alias BFS 使用缓存 adjacency/multi-source BFS；
- case 两两互斥的 `O(k²)` SMT 改为一个 `O(k)` exactly-one cardinality；
- Scheduler 删除 `GSON.toJson(...).contains(regionId)`，改用 typed region index。

增量 `z3 -in` 独立为最后一个性能 PR；先证明与当前逐 valuation 启动 Z3 语义等价。

截至 2026-07-25，PR 6 已实现第一轮算法替换。静态 backward analysis 不再最多 96
轮扫描全部 selected methods，而以 method/state dirty queue 驱动固定点；runtime planner
一次构建 call tree、method/runtime/field event 与 invocation ordinal 索引，root 只读取
自身 subtree，字段 latest-writer 改为有序表二分；Composer 一次构建
`SummaryIndex`，producer resolution 和 binding lookup 不再反复全表扫描，equality
传播改为邻接 worklist，case partition 从两两互斥的 `O(k²)` 约束收敛为一个线性
exactly-one cardinality。

同一轮删除了 output slice 中零生产消费者的 `causalEdgeCount`、静态 scope 镜像、
`excludedAlternative*` 和 `prestateElisions`，以及 heap coverage 只用于展示的 match/gap
对象和无消费者计数。`complete/runtimeRefinementComplete`、`staticSites`、canonical
edge ID、transformer issue、capture/read-from/object identity 等准入证据保持不变。
Scheduler 也不再序列化整个 alternative writer group 后做字符串 `contains(regionId)`
筛选；精确 selected binding 本身就是 typed instance gate。PMD unused-private 审计后的
零消费者方法、字段和参数同步删除。该里程碑生产 Java 净减少而不是把索引代码叠加到旧
实现上。57 项快速回归、baseline 单独端到端和干净 worktree 的 13-fixture 并行真实
Z3 矩阵均已通过；矩阵零失败并保持 6 `SAT/REACHABLE`、7
`UNSAT/UNREACHABLE`。

### PR 6 后续：删除 current-schema 内部镜像

PR 0–6 完成后继续按 field ledger 做原子切换，不恢复历史 artifact 兼容：

- heap transformer admission 只接受
  `requestedStateTransformerContractVersion=1` 的 exact obligation。已删除按 observed
  effect 数量猜测 write-site coverage、把任意无 edge 的 `void` slice method 当作
  transformer，以及 historical-slice 分支；contract 缺失或错误仍由 Importer fail
  closed；
- dynamic container field binding 的 selector 只存在于 canonical
  `containerSelector`。Runtime 不再同时写九个 flat mirror，Solver、Runtime、
  Importer、Composer 和 robustness shell 已一次性切换到 nested selector；
- dynamic container field binding 已一次性升到 V3。删除
  `actualHookSiteId/actualHookOccurrence`、`effectiveMaterializationSiteId/
  effectiveMaterializationOccurrence` 和四个 `materializationSiteBridge*` 镜像；
  static declaration、canonical selector、field path、activation-local object identity
  与 field observation join 仍提供实际证明。Runtime、path solver、replay validator、
  Importer、Composer 和 robustness shell 只接受 V3，V2 不提供 fallback；
- field observation 只记录 observation 自身的 path、owner/value identity、expression
  和唯一 `dynamicBindingId`。完整 binding、container selector、bridge、key 与 capture
  metadata 只存在于 `dynamicFieldBindings`；Importer 通过唯一 ID 做 join，不再逐字段
  比较同一 Runtime writer 生成的副本；
- instrumentation coverage admission 只判断能否安全使用 bounded closure：唯一选中
  activation、可执行 admission、合法且 complete 的 canonical `outputClosure`，以及
  capture/heap-discharge gate。Z3 assignment、branch replay、exact heap obligation
  仍分别由 Runtime 与 Importer 在真实 trust boundary 校验，不在 instrumentation
  selection 中重复实现。

这些删除不是弱化证明：canonical binding、object token/scope、field path、read-from、
transformer obligation、branch contract 和所有 Importer/Composer gap gate 均保留。
截至 `2b051a69`，手写生产 Java 为 78,115 行，相对 81,581 行冻结基线累计净减
3,466 行。57 项快速回归和干净 worktree 的 13-fixture 并行真实 Z3 矩阵再次通过，
保持 6 `SAT/REACHABLE`、7 `UNSAT/UNREACHABLE`、零 failure；本轮日志目录为
`target/robustness-matrix-logs/20260725T070326Z.1081674`。矩阵曾准确暴露 path
solver 遗留的 V2 reader，修复后 `containers` 与 `unreachable-parity` 的多轮 campaign
分别恢复为 `sat` 与 `unsat`，说明 schema cutover 覆盖了 seed、worklist、solver、
replay、merge 和 compose 全链路。61k–69k 仍是后续净删除目标，不把尚未实现的行数
写成完成结果。

截至 `0c1f9dda`，下一批 current-schema 镜像清理也已完成。Scheduler 不再构造和打印
无人读取的 summary；随 summary 唯一消费者一起删除了全局 `UnionFind`/
`equalityClasses`，而每个 activation 的 witness-bearing equality closure 仍在
`contextFor()` 中按 canonical relation 构造。Solver、Runtime、Importer、Worklist、
Merger 与 Composer 中只用于展示的计数、固定 authority、code-position 和重复 identity
镜像同步删除；solver status/SMT hash/model assignment、完整 branch/VM attestation、
canonical observation/binding ID、object identity、read-from 和所有 fail-closed gap
保持不变。PMD 审计只剩一个已核对为真实 comparator 读取的 `TargetBranch.branchIndex`
误报，57 项快速回归通过。

手写生产 Java 现为 77,812 行，相对 81,581 行冻结基线累计净减 3,769 行。隔离干净
worktree 的 13-fixture 并行真实 custom-JDK/Z3 矩阵再次零失败，保持 6
`SAT/REACHABLE`、7 `UNSAT/UNREACHABLE`；日志目录为
`target/robustness-matrix-logs/20260725T073029Z.1308684`。

截至 `ea8639eb`，七套阶段私有的 forgiving JSON field reader、六套 SHA-256 和四套
permissive JSONL reader 已由 `JsonFields`/`ArtifactIO` 唯一实现替代；malformed 或
non-object JSONL row 现在在 artifact boundary 一致 fail closed，不再被个别阶段静默
跳过。Replay admission 也只剩一个职责边界：Importer 校验 branch、完整 model
assignment 与 canonical output closure，ReplayValidator 只校验不能由 payload 推导的
fresh Map.Entry/container activation-local selector rebinding。原 replay 测试从 532 行
收敛到 231 行，直接覆盖 fresh map 成功和错误 object-token scope 拒绝。

手写生产 Java 现为 77,112 行，相对冻结基线累计净减 4,469 行。57 项快速回归、
generic workflow shell test 与隔离干净 worktree 的 13-fixture 并行真实
custom-JDK/Z3 矩阵全部通过，仍为 6 `SAT/REACHABLE`、7
`UNSAT/UNREACHABLE`、零 failure；日志目录为
`target/robustness-matrix-logs/20260725T075103Z.1490066`。

截至 `f48efa8d`，剩余八个 concolic value/query stage 的 forgiving JSON field
reader 也已收敛到 `JsonFields`。Importer 不再输出无人消费的命令行 summary 和
`skippedEventCount`；Scheduler、target query 与 raw runtime result 删除了可由
canonical admission、数组或 gap 推导的 readiness、count、authority 和 VM
内部校验镜像。数组的 symbolization expression、activation-local identity、
consumed leaf、model assignment、branch witness 唯一性与所有 fail-closed gate
仍保留并继续参与准入。robustness shell 同一提交切换为直接校验 canonical
`constraints`，没有保留旧字段 fallback。

手写生产 Java 现为 76,912 行，相对冻结基线累计净减 4,669 行。57 项快速回归、
generic workflow shell test 与隔离干净 worktree 的 13-fixture 并行真实
custom-JDK/Z3 矩阵全部通过，仍为 6 `SAT/REACHABLE`、7
`UNSAT/UNREACHABLE`、零 failure；日志目录为
`target/robustness-matrix-logs/20260725T080803Z.1672266`。

下一批继续执行“全新 schema、无 fallback”的原子切换。Scheduler 现在必须消费
canonical static graph，删除了 graphless `DefinitionIndex` 和 local-name 猜测路径；
Planner 直接把 canonical typed region/edge row 交给 writer，不再在同一进程中
deep-copy 后用 `StaticRegionArtifactSchema` 重复验证自己刚生成的数据。真正跨 artifact
的 decoder、ID join 和 fail-closed gap 仍保留。

Instrumentation selection 只负责它自己的最小准入：唯一 activation、可执行 admission、
complete canonical `outputClosure` 和 exact heap discharge。branch replay、model
assignment、bundle identity 等仍在实际 Runtime/Importer trust boundary 校验，不在
selection 阶段复制一套。五个 branch/closure value codec 也不再拒绝未来无害的附加
JSON key，但 schema/kind、所有必需语义字段、类型、canonical ordering、capture ledger
和 completeness 仍严格校验。Runtime、Importer 与 Composer 同步删除了只供展示的
engine-array location、map expected-count、heap effect method/result/normalization 以及
fatal/bounded-region reachability镜像。

该批 baseline generic workflow 已完整闭合 target 和两个 producer worklist，Composer
无 gap，Z3 报告 `REACHABLE`。手写生产 Java 为 76,441 行，相对 81,581 行冻结基线累计
净减 5,140 行。对应里程碑 `0233c247` 的隔离干净 worktree 13-fixture 并行真实
custom-JDK/Z3 矩阵零失败，保持 6 `SAT/REACHABLE`、7
`UNSAT/UNREACHABLE`；日志目录为
`target/robustness-matrix-logs/20260725T083622Z.1899755`。

截至 `1abd8085`，branch replay 的唯一事实载体已经收敛为 typed
`BranchWitness`：raw result 不再并列输出 outcome、condition index、PC size 和 VM
authority 镜像，Importer 通过 canonical witness 与 activation-owned raw PC 在
trust boundary 做一次完整 replay-contract 校验。随后一批继续删除 Runtime 中同一
contract 的重复验证、只供展示的 replay positions、Composer 的 `MergeStats` 名称
计数、Runtime Planner 的无人读取 warning/counter，以及静态 region 的 seed-guard
诊断镜像。缺失或不可读的必需静态 artifact 现在直接报具体路径并终止；合法但不完整的
output closure 仍通过 canonical issue/gap fail closed。

这一轮首次 clean matrix 暴露的是 robustness shell 仍读取已经退休的
`allModelAssignmentsApplied`，而对应 container 候选本身已为 `SAT/REACHABLE` 且无
gap。这是一次性 schema 切换遗漏的旧 shell reader，不是 path exploration 漂移；脚本
已改为检查 canonical `modelAssignmentsApplied` 唯一 key/value 集合。当前手写生产
Java 为 76,091 行，相对冻结基线累计净减 5,490 行；57 项快速回归通过。对应里程碑
`247c5b1c` 的隔离干净 worktree 13-fixture 并行真实 custom-JDK/Z3 矩阵也已零失败，
保持 6 `SAT/REACHABLE`、7 `UNSAT/UNREACHABLE`；日志目录为
`target/robustness-matrix-logs/20260725T090733Z.2280847`。

下一批把 artifact 中可由 canonical collection/state 直接推导的计数和固定说明继续原子
删除：path worklist 只保留 `state`、实际 worklist 和 observed paths；target query、
merged relation、Composer manifest、static coverage、Map projection、transformer
obligation、VM placeholder 与 fresh-map initializer 均以实际数组、typed identity 或
constructor signature 为事实源。Java、shell 和测试 reader 已在同一批切换，没有旧字段
fallback。

同时，包级调用审计确认 output-independence branch 只有 reader 而从无生产 writer，故其
`PATH_ASSUMPTION` 路径在真实执行中不可达。该伪协议及相关 authority/reason/checked-output
字段已整体删除；output slice 内的 causal branch 统一维持 `EXPLORE`，branch witness、
solver path context 和 required successor evidence 不变。十个零调用 helper/API 也一并
退休，避免保留“看似支持、实际无人调用”的表面积。

手写生产 Java 为 75,769 行，相对 81,581 行冻结基线累计净减 5,812 行。57 项快速
回归、PMD、generic shell 语法和真实 baseline 均通过。对应里程碑 `2b165d25` 的隔离
干净 worktree 13-fixture 并行真实 custom-JDK/Z3 矩阵也已零失败，保持 6
`SAT/REACHABLE`、7 `UNSAT/UNREACHABLE`；日志目录为
`target/robustness-matrix-logs/20260725T124250Z.2537011`。

下一批继续删除阶段私有的重复基础设施，而没有增加新的 schema 层。五个 JSONL
原子替换 writer 和两个 unique-ID index builder 现在分别由 `ArtifactIO.replaceJsonl`
与 `ArtifactIO.uniqueIndex` 唯一实现；Importer 的最后一组 forgiving field accessor、
四个 branch value 类型中的 primitive decoder、OutputClosure 的 Java descriptor
validator，以及 runtime trace 的 JSON string/object serializer 也分别复用
`JsonFields`、`JavaPrimitiveSmtSemantics` 和 `CausynthJson`。这些是现有 canonical
语义的唯一实现，不是 wrapper 搬家；原局部实现已删除。

Concolic 插桩此前会为 root、materialization、capture 和 bounded-closure readiness
分别扫描同一 activation JSONL。现在每次 Soot instrumentation 只构造一次不可变
`InstrumentationPlan`，四类 selection 从同一组选中 row 派生；malformed/non-object
row 在这个 artifact boundary 一致拒绝。输出 closure、capture binding、heap discharge、
executable admission 与 bundle `ALL` 语义保持不变。手写生产 Java 当前为 75,417 行，
相对 81,581 行冻结基线累计净减 6,164 行；57 项快速回归、PMD 和真实
custom-JDK/Z3 baseline 均已通过。对应里程碑 `8be93716` 的隔离干净 worktree
13-fixture 并行真实 custom-JDK/Z3 矩阵也已零失败，保持 6
`SAT/REACHABLE`、7 `UNSAT/UNREACHABLE`；日志目录为
`target/robustness-matrix-logs/20260725T131337Z.2802421`。

Trace aggregation 也切换为 parse-once：offline aggregator 对每条 runtime trace row
只调用一次 Gson parser，后续 Method/Field/Execution event 共享该 `JsonObject`；
原来按字段动态编译/缓存正则、重复扫描整行以及手写 JSON unescape 的实现已删除。
这同时正确处理标准 Unicode escape，避免不同字段 decoder 对同一 row 得出不同结果。
手写生产 Java 进一步降至 75,330 行；57 项快速回归、PMD 与真实
custom-JDK/Z3 baseline 通过。对应里程碑 `89fde48a` 的隔离干净 worktree
13-fixture 并行真实 custom-JDK/Z3 矩阵也已零失败，保持 6
`SAT/REACHABLE`、7 `UNSAT/UNREACHABLE`；日志目录为
`target/robustness-matrix-logs/20260725T132252Z.2990822`。

下一批并行收敛 static、runtime 与 Composer 三条链，但仍只保留一个 canonical
事实源。静态 region port 现在由 Planner 一次性写入 `javaType`，Composer 与 Boolean
extractor 删除 `symbol`、`declaredType` 和从 cell 再猜类型的 fallback。Transformer
contract 的 output port/cell 由外层 output slice 唯一给出，固定 version/applicable/
authority 也已退休；obligation、target cell、causal edge 和 complete/issues 继续作为
heap correctness gate。Runtime output slice 只写唯一 `complete` 与实际 issue/obligation/
capture 集合，不再镜像 structural、truncation 和 refinement 布尔。

Runtime raw result 删除了 CALL_ARGUMENT 上无人消费的 concrete class，以及已在顶层
canonical observation ledger 中出现的 per-capture Map projection 副本；object identity、
expression、field-flow 与 fail-closed observation 仍完整保留。Composer manifest 删除零生产
reader 的 `resolvedProducerKeys`，relationship row 只保留 Boolean discovery 实际读取的
kind/roles，公式继续由 named SMT assertion 唯一承载。Boolean truth table 已穷举所有
`2^N` Boolean root valuation，因此删除了随后重复证明同一 DNF 的额外 Z3 process；
任何 unknown 仍产生 gap 并 fail closed。Manifest 仍以 SHA 绑定 SMT、static regions、
fatal query、summaries 和 relationship artifact，Boolean report 通过该 trust-root manifest
引用它们。

该批手写生产 Java 为 74,753 行，相对 81,581 行冻结基线累计净减 6,828 行。
57 项快速回归、PMD、shell 语法与真实 custom-JDK/Z3 baseline 均通过；baseline 仍为
`SAT/REACHABLE`，所有 composition/worklist/importer gap 均为空。对应里程碑
`636d0f85` 的隔离干净 worktree 13-fixture 并行真实 custom-JDK/Z3 矩阵也已零失败，
保持 6 `SAT/REACHABLE`、7 `UNSAT/UNREACHABLE`；日志目录为
`target/robustness-matrix-logs/20260725T134650Z.3220406`。

下一批把“一个事实多次表示、一个 payload 多层重复验证”继续收敛为唯一语义载体。
ReplayValidator 从约一千行缩到只负责 activation-local dynamic selector、fresh
Map.Entry 与 container token rebinding；普通 schema、model assignment、branch 和
output-closure 验证只在 Importer artifact boundary 做一次。Worklist 不再持久化
`observedPathCount`，target path 不再持久化重复 `pathKey`，merge manifest 只写 typed
`gaps`，唯一完成 gate 仍是 relation 的 `relationallyComplete`。

Scheduler/Solver 同时删除了可由 admission、status、value type 和 canonical selector
推导的 readiness、调用状态、退出码、浮点格式与 nested selector 副本。Runtime Planner
删除旧 frozen-static-accessor artifact fallback；新 schema 必须提供 canonical static
port metadata，缺失时直接拒绝，不猜历史产物。runtime alias、field-path 与 map
projection 中的固定 authority/计数/ready 镜像也已退休，但 event sequence、对象身份、
field path、selector、causal edge、capture 与所有 admission blocker 均保留。

该批手写生产 Java 为 73,822 行，相对 81,581 行冻结基线累计净减 7,759 行；本批净删
931 行生产代码。57 项快速回归、PMD、shell 语法与真实 custom-JDK/Z3 baseline 均通过；
baseline producer worklist 正常闭合，Composer/Importer 无 gap，Z3 仍报告
`SAT/REACHABLE`。对应里程碑 `e96b618d` 的隔离干净 worktree 13-fixture 并行真实
custom-JDK/Z3 矩阵也已零失败，保持 6 `SAT/REACHABLE`、7
`UNSAT/UNREACHABLE`；日志目录为
`target/robustness-matrix-logs/20260725T141052Z.3416779`。矩阵只读取里程碑 commit，
没有读取或覆盖主 worktree 中的用户 fixture 修改。

下一批继续沿 trust boundary 删除“写出后无人读取”和“同一 payload 内重复证明”的
代码。Runtime Planner 的三个静态 JSON artifact 现在各自只由 Gson 解析一次，原手写
字段扫描器和 unescape 已删除。Instrumentation selection 由一个 typed
`InstrumentationPlan` 原子选择唯一 activation，并一次派生 root、materialization 与
capture；不再跨 activation 合并，也不再为同一 output closure 重复 decode 和扫描。
静态 symbolic coverage 只保留最终 admission boolean，删除没有执行消费者的 seed-guard、
accessor、dispatch 和计数诊断对象。

Runtime raw result 的 model assignment 只写 Importer 实际 join 的 canonical key/target/
value core；dynamic container/Map assignment 另外保留 ReplayValidator 实际 join 的
activation-local selector/rebinding witness。engine-array 注册、branch mapping base row
和 exact consumed-field 校验各自合并为一个实现。Importer 删除只在方法内部写后再读的
Map-state 镜像、未消费的 target
root/execution metadata，以及 heap effect 的 normalization/authority/output-binding 展示
字段；raw PC index、site/occurrence、对象身份、表达式、input/output port、capture 与
transformer obligation 均保留。Composer 只接受 canonical guarded path merge，不再把
raw single-path、`protocolModel`、`explicitContracts` 或缺失 summary 的自由谓词当成
可组合语义。Solver 对无法精确编码的 Java IR 直接产生 typed unsupported/gap，不再为
“可打印 SMT”发明 uninterpreted function 或 diagnostic free variable。

这次一次性退休 target summary 的 `executionKind` 时，真实 baseline gate 发现 Scheduler
仍有一个遗留 reader，表现为 target seed 已成功 Import、但没有生成 solver query。该
reader 已删除，并增加一个只锁定 canonical target-summary contract 的聚焦回归；没有恢复
双写或 fallback。修复后 target 与两个 producer worklist 均闭合，Composer/Importer 无
gap，真实 Z3 再次报告 `SAT/REACHABLE`。当前手写生产 Java 为 72,113 行，相对
81,581 行冻结基线累计净减 9,468 行；62 项快速回归通过。这是首次 baseline gate
通过时的数值；下面的 clean-matrix 修复恢复了少量真实 correctness evidence。

首次 clean matrix 又准确指出两项 field-ledger 分类错误：non-null `String` 的 VM
symbol 使用 `M_L'RuntimeType'_PORT_owner`，不是 primitive/reference field 的统一前缀；
fresh Map.Entry/container assignment 的 applied selector 也是 ReplayValidator 的真实
correctness consumer，并非展示镜像。Solver 现在精确解析这两类合法 VM symbol envelope，
仍不恢复任意 substring/normalized fuzzy match；Runtime 只恢复 planned static selector
与当前 activation-local selector/key join 所需字段，不恢复 concrete-class 等诊断字段。
两个聚焦回归分别锁定 typed String materialization 和 canonical dynamic rebinding。
Container workflow 随后完整闭合并得到正确 `SAT/REACHABLE`，但 matrix 的最后一个
shell assertion 仍读取已退休的
`dynamicFieldBinding.entryValueRefWitnessJoinCertified`。该 assertion 已原子切换到
Composer 真正消费的 canonical `heapObservation.valueExpressionWitnessCertified`
及其 activation-local object token/scope，同时继续逐项校验 binding ID、field path 与
key expression join；没有降低 container 语义门槛。

最终里程碑为 `37075131` 加修复提交 `1b905274`。手写生产 Java 为 72,214 行，相对
81,581 行冻结基线累计净减 9,367 行；63 项快速回归、PMD 与 shell 语法通过。`1b905274`
的隔离干净 worktree 13-fixture 并行真实 custom-JDK/Z3 矩阵零失败，保持 6
`SAT/REACHABLE`、7 `UNSAT/UNREACHABLE`；日志目录为
`target/robustness-matrix-logs/20260725T150913Z.3893832`。矩阵只读取提交后的 clean
worktree，没有读取或覆盖主工作树中的用户 fixture 修改。

下一批继续执行“不过度校验、不过度设计，但不删除不可重建的 correctness evidence”：

- 删除 Runtime Planner 的 mapping-only producer 扩展和旧 accessor-return discovery
  recovery；新版本只接受 canonical static graph 与真实 `FIELD_READ`。
- `EngineArrayInputBinding` 一次性切到 schema V2。row 只保留 activation、input
  port/cell、descriptor、VM array id、activation-local object token 和 finite-array
  expression；十个固定 authority/`true`/同值别名不再跨层传递。Runtime 仍在唯一能访问
  live Java array 的位置检查同一对象、reflection length、连续 element、provenance/type
  以及 concrete primitive literal 的逐元素相等；Importer 保留唯一 input/action/VM-id
  join，Composer 不再第三次重复整份证明。
- 静态 field declaration 只保留 `declaredFieldSignature`。owner/type/name 只在
  static-to-scheduled execution boundary 严格解析一次，供 runtime object/field hook
  使用，不写回静态 artifact。真实 container gate 暴露过一次遗漏：signature 已在
  static row 中，但 scheduled container declaration 未派生 execution tuple，造成
  `0 complete runtime bindings`。修复只补这一派生，不恢复旧静态 tuple 或 fallback；
  `unreachable-parity` 随后再次完整 CLOSED、merge/compose `gaps=[]`、Z3 `UNSAT`。
- Replay admission 以 canonical `modelAssignmentKey` 和唯一 `dynamicBindingId` 连接
  plan/applied/raw/imported row；fresh Map.Entry 的当前 key/observation 和 container 的
  activation-local token/scope/selector 仍必须逐项存在，不能从 seed identity 推导。
- Solver 删除宽松的私有 S-expression tree，复用严格 SMT application splitter；任何
  unsupported 语义都产生 typed gap 和 `(assert false)`，不再发明 diagnostic free
  constant/UF。Boolean root report 删除无生产消费者的 javaType/sort/case projection
  镜像，但保留 descriptor、solver term、String nullness term、完整 valuations 与
  reach condition。

该候选里程碑手写生产 Java 为 70,606 行，相对 81,581 行冻结基线累计净减 10,975 行，
本批净减 1,608 行。63 项快速回归、PMD report、shell 语法和 `git diff --check` 已通过。
主工作树矩阵中的 12 个未改 fixture 保持预期；用户正在编辑的 container fixture 的两个
producer 也都 CLOSED 且 merge/compose `gaps=[]`，但其修改后语义为 `UNSAT`，因此不拿旧
SAT profile 断言评价该文件。权威 6 SAT/7 UNSAT release gate 仍必须在不含该用户修改的
clean commit worktree 上通过后，才记录本批为已完成。

提交 `a380e791` 已在独立 clean worktree 以 13 个外层 worker 完成权威矩阵：
`completed=13 failures=0`，保持 6 SAT/7 UNSAT。日志目录为
`target/robustness-matrix-logs/20260725T161007Z.147459`。这确认 signature-only field
declaration、EngineArrayInputBinding V2、replay/solver/boolean/trace 收敛没有改变既有
deterministic shared-field RPC 语义。

下一里程碑完成第一轮目标，不为行数删除 correctness evidence：

- 删除独立 `ConcolicReplayValidator`。Importer 在唯一 replay admission 中用 canonical
  `modelAssignmentKey` 和唯一 `dynamicBindingId` 连接 plan/applied/raw row；fresh
  `Map.Entry` 的当前 key/observation，以及 container 的 activation-local
  token/scope/selector 仍逐项检查。Branch replay 一次性切到 Contract V2，
  `BranchReplayPlan` 删除；contract 直接携带 exact code position/site/occurrence/
  outcome、predicate witness 与 solver path context，observation validator 只做一次
  event uniqueness/order/outcome/predicate 校验。
- Scheduler 删除 array materialization 的第二次准入、固定空 admission/schedule 镜像；
  definition-site、field-path 与 object identity 仍由各自 canonical boundary 检查。
  Composer 的 producer region 只来自 `outputClosure`，resolved edge 内部只保留已准入
  binding+summary；event sequence、receiver/value identity、mutation invocation 和
  fingerprint 仍在 `AutomaticRegionEdge` 唯一准入边界验证。missing/incomplete/unbound
  四套集合合并成唯一 `COMPOSITION_GAP`，仍直接关闭候选。
- `MAP_ENTRY_READ`、`FINITE_MAP_ENTRY_SNAPSHOT` 与
  `MAP_STATE_INPUT_OBSERVATION` 原子升级 V2。canonical `entries` 保存实际 key/value
  expression 和 object token；删除并行数组、四份 size 镜像、固定 true 的稳定性字段、
  五个 binding-complete 镜像和 warning。Runtime 对 live Map 的双遍历、顺序/identity、
  `map.get`/`containsKey` 与 unresolved fail-closed 没有删除。
- Runtime trace 只保留一种生产路径：workload JVM 流式写 canonical trace 和 CLOSED
  manifest，host JVM 检查 `complete && !truncated && !writeFailure` 后离线聚合。删除
  workload JVM 同时保留第二份 Method/Field/Execution DTO 并在 shutdown 内聚合的模式；
  recorder 与 planner 共享 canonical event carrier。baseline trace 实跑得到 88 rows、
  CLOSED/complete manifest、5 activations 和 6 runtime edge rows。
- 静态 MethodFacts/Builder 中间层并入 `StaticGraphIndex`，不再第二次全扫 edge。
  projected-edge fixed point 删除每轮复制并扫描全部已有 edge 的路径，改成 endpoint
  index + dirty projected-edge queue；edge-before-demand 与 demand-before-edge 都由同一
  增量规则覆盖，没有保留旧算法 fallback。小 fixture 的时间差仍在噪声内，因此只声明
  复杂度收益，不夸大为已证明的 wall-clock 加速。
- Boolean extractor 不再二次解析 Composer 已 hash 绑定的 case projection catalog；
  保留 canonical roots、所有 valuations/gaps 和 reach condition。Solver 的 Java type、
  primitive cast 与 integer literal 统一到现有 typed codec/semantics，并删除无 reader
  的 solver/model/gap 镜像；unsupported 仍不调用 Z3。

该候选手写生产 Java 为 69,271 行，相对 81,581 行冻结基线累计净减 12,310 行，
本批净减 1,335 行，进入第一轮“约 61k–69k / 净减 12k–20k”的目标区间。一次
`mvn clean test` 的当前精简回归集为 62 项，零 failure/error/skip；PMD/CPD report、
generic workflow shell test、shell syntax 与 `git diff --check` 通过。此前未 clean 的
Surefire 目录残留了已删除测试类的 XML，所以不再把那个 68 计数作为验收数字。

提交 `0a23609f` 随后在不含用户 container 修改的独立 clean worktree 完成最终权威矩阵：
`completed=13 failures=0`，保持 6 SAT/REACHABLE、7 UNSAT/UNREACHABLE；日志目录为
`target/robustness-matrix-logs/20260725T165202Z.410183`。

通过后又做了一次 retired-code audit。独立 `ConcolicReplayValidator`、
`BranchReplayPlan`、双 trace mode、Map V1 镜像和旧 activation/merge/Composer shell
reader 均已消失；旧 artifact 只允许在 canonical decoder 中作为明确拒绝条件出现，不再
存在兼容执行路径。审计发现 shell debug projection 仍读取
`candidateRelation`、三个 readiness boolean、case `pathKey` 镜像和 Composer V1 计数；
这些 reader 已原子切到 canonical edge state、`admission`、relation cases 和 Composer
V2 `state/trustState/gaps/artifact`。Runtime selector 中一个对永远非空
`RootContextSelector` 的 null compatibility 分支也已删除。其余命中 “fallback/legacy”
的代码均有实际生产消费者，或表达 fail-closed 禁止降级的语义，不能为了字符串清零而删。
清场后手写生产 Java 为 69,269 行，相对冻结基线累计净减 12,312 行。
清场提交 `200bd576` 的独立 clean worktree 随后再次完成全部 13 个真实
custom-JDK/Z3 fixture：`completed=13 failures=0`，仍为 6 SAT/REACHABLE、7
UNSAT/UNREACHABLE；日志目录为
`target/robustness-matrix-logs/20260725T170553Z.599731`。该结果是最终 release gate，
主工作树中未暂存的用户 container fixture 修改没有进入构建、提交或矩阵。

closure-goal follow-up 由 `30dd0704`、`d4fe4ee8`、`98d30d89` 三个里程碑完成并推送：
同一个动态 region instance 现在只保存一个 `RegionInstancePlan` envelope，语义需求是
嵌套的 `OUTPUT_RELATION` / `TARGET_REACH` closure goal，branch flip 只产生
`PathQuery` / `ExecutionTask`，不再伪装成 `ACT.UPSTREAM.*` 或 `ACT.PATH.*`。
primitive field 的 no-write path 由 same-cell `HEAP_PRESTATE`、唯一 root-to-owner
field path、入口真实 prestate symbolization 和全部正常出口的 final-field capture 共同证明；
不再追踪哪一个 assignment 最后写入，也不把 seed occurrence 固化到翻转路径。
这一轮同时删除 test-only Scheduler output 准备路径、重复 canonical JSON、旧 bundle
清理和多余计数镜像。当前手写生产 Java 为 69,696 行；新增行属于此前缺失的 frame
correctness，不为进入某个行数区间删除证明。

提交 `98d30d89` 的 62 项快速回归全部通过。随后在不含用户 container 修改、但使用相同
custom-JDK build 的独立 clean worktree，以 13 个外层 worker 再跑真实 concolic/Z3：
`completed=13 failures=0`，保持 6 SAT/REACHABLE、7 UNSAT/UNREACHABLE；日志目录为
`target/robustness-matrix-logs/20260725T193226Z.1354005`。主工作树中用户修改后的
container 也单独完成所有 closure，`gaps=[]`，按其当前约束得到 UNSAT；该文件没有进入
上述提交或权威矩阵。

最新 schema 收敛继续遵守“不过度验证、不过度设计”：字段声明、projected field path 和
exact leaf declaration 只由 `FieldPathSpec` 解析；静态输入的 field/accessor
materialization 只由 `MaterializationSpec` 携带；Scheduler 产生的 worker 输入只使用
`InputActionCatalog.inputActions`，不再同时传递 `symbolize`、`materializations` 和
`concreteFallbacks` 三份执行视图。静态 output slice 的未解决输入也只保存
`inputGaps`，`complete` 由 gap 是否为空推导。旧字段不保留 writer、reader 或兼容
fallback。

该切换后的干净 core workflow 已逐个验证 baseline、cross-method-fields 和 multitype：
三个候选均 `gaps=[]`、relation worklist `CLOSED`、真实 Z3 为 `sat`；其中
cross-method-fields 覆盖深层 object.field/accessor materialization，multitype 覆盖
`int/long/double/String/Boolean`。下一步不是再增加 proof wrapper，而是在 Importer 为每个
raw execution 建一个保留重复 row 的只读 `EvidenceIndex`，让完整 capture composite、
site/occurrence、event sequence 和 object identity 继续 fail closed，同时删除 joint-output
member 之间对相同 capture、branch、dynamic-field 和 input-action evidence 的重复扫描。

随后 static artifact 也只保留可重建 runtime closure 所需的事实。region 顶层不再写
truncation 镜像；output slice 不再写 selection、regionTruncated 和五个
complete/truncated boolean，Runtime 由 `truncationReasons + causalEdgeIds + inputGaps`
唯一推导 readiness。region edge 不再携带固定 order/object-identity、relation/evidence
或 mapping authority 镜像；所有 edge 仍无条件执行 event order 检查。frame prestate
只由 `HEAP_PRESTATE + bindingAuthority` 识别，不再额外写 `frameConditionInput=true`。
该切换净减 89 行生产 Java，62 项快速回归以及同一三个真实 core workflow 全部通过。

下一批把“同一事实只解析、索引、选择一次”落实到四条主链。静态分析的
`CausynthAnalysisResult` 与 Planner `Result` 已合并为唯一 `StaticProgram`，Analyzer、
Assembly、Instrumentation 和 ArtifactWriter 不再逐层复制同一 program。Runtime Planner
预建 anchor/method 索引并合并 readiness 扫描；Importer 为每个 execution task 只 decode
一次 `InputActionCatalog`，再用保留重复 row 的 `EvidenceIndex` 共享 capture、heap、
field、branch、projection 和 dynamic-binding evidence；Composer 同样只 decode/cache
一次 summary closure 与 canonical payload，并复用 context relation、edge-binding 和
causal reachability 索引。所有唯一性检查仍在各自 trust boundary 以保留重复 row 的方式
执行，没有用 `Map` 静默覆盖证据。

这一批同时修复了 schema 切换暴露的 nested-field sort 缺口：静态 port 顶层
`javaType` 可以表示 field path 的中间对象，但 custom-JDK 实际 symbolized 的是
`materialization.javaType` 指定的叶子。Composer 现在从 canonical materialization 取得
logical port type；否则 `StateNode.state.guard.enabled` 会被错误地按 `GuardNode` 而不是
`boolean` 建模，并产生 `BASE_PORT_FIELD_TYPE_MISMATCH`。聚焦测试锁定这个 contract。
当前手写生产 Java 为 69,483 行；用户未提交的 container 变体已完整闭合为
`gaps=[] / CANDIDATE_READY`，并按其当前约束由真实 Z3 得到 `UNSAT`。官方 fixture 的
SAT/UNSAT release gate 必须继续在排除该用户修改的 clean worktree 运行。

删除旧 slice `complete` 镜像后，Planner 内部也不得继续读取该字段。所有内部
producer-demand 与 canonical-output 选择统一调用同一个推导：truncation 与 input gap
为空、causal edge 非空、capture complete，且适用时 transformer contract complete。
这修复了“wire writer 已删除但类内旧 reader 把所有 slice 判为 incomplete”的原子迁移
遗漏，同时没有恢复第二份 readiness boolean。

随后三条独立旧路径被原子收敛。`ConcolicRegionRuntime` 删除了从无 Scheduler/Planner
writer、且 Importer 明确拒绝的 whole-task `concreteReplayOnly/observationOnlyReplay`
模式；action-level concrete materialization、normal-exit final-field capture、read-from 与
object identity 均保留。`RegionPathWorklist` 成为 relation closure 的唯一 authority，只在
`CLOSED + OUTPUT_RELATION_CLOSURE` 时生成原有 wire-compatible guarded relation，
因此独立 `RegionSummaryMerger` 及其第二遍 scope/path/evidence 校验被删除。Soot 插桩侧
两套巨型 hook holder 合并为一个 typed `HookCatalog`，三份 primitive
box/pause/materialize/resume/unbox 模板合并为唯一 round-trip emitter。

logical input port 类型也统一由 `MaterializationSpec.logicalJavaType()` 给出；Composer 和
Boolean reach extractor 不再分别把 nested field 的中间 owner 类型当成 leaf 类型。这既
决定 SMT sort，也决定 Boolean root catalog。里程碑 `95a9fc58` 已在隔离 clean worktree
通过全部 13 个真实 custom-JDK/Z3 fixture，结果保持 6 个 `REACHABLE/sat`、7 个
`UNREACHABLE/unsat`、0 failure。

后续小批次继续只删除重复事实：Planner 直接复用 canonical `DeclaredField`，Composer
只在 relation 真正消费点执行一次 admission，Scheduler 不再把
`runtimeDefinitionMethods` 泄漏到 execution task，也不再重复 deep-copy/rewrite 已由
goal projection 携带的 `goalKind` 和 `outputClosure`；同一 target goal 的多个 branch
共享一份不可变 materialization plan。

下一批删除 static fact 的未读 carrier/扫描，让 RPC mapping 直接保存 canonical method
signature；Runtime Planner 对强制的 frozen static graph 采用唯一严格 reader，删除
“部分读入后再下沉 gap”的半有效 catalog 状态，并合并事件排序与 readiness 扫描；
Importer 只信任 canonical `InputActionCatalog` 和 versioned output closure，不再重复读取
static region input schema，也不再保留缺 `captureBindingId`/`captureKind` 的旧 fallback。
坏静态图现在在读取边界给出明确异常，而不会继续产生貌似可执行的 activation。当前手写
生产 Java 为 68,654 行。

容器字段执行 contract 随后一次性切到 schema V2 `CONTAINER_SNAPSHOT`：Runtime 在首次
container observation 按 exact index/identity、declared owner/type、occurrence 与
activation-local object token 原子 materialize，删除已无 writer 的 V1
`FIELD_ACCESS_HOOK` 二次 selector；后续 owner-wide hook 只复用 binding 或作为 readback
忽略，region-exit coverage gate 仍保留。InstrumentationPlan 直接持有 canonical capture
list，不再建立第二个 wrapper/index；Worklist 为每个 summary 一次构造 `SummaryPath`，
供 path key、branch mapping、coverage、flip task 和 CLOSED relation 共同消费。此时手写
生产 Java 为 68,304 行。

Map projection replay 不再把同一个 selector JSON 展开为 28 个字段镜像，而是在
`ModelAssignment` 中保留一份 canonical selector 并按需验证全部 identity、index、
occurrence、owner/type/signature、key、token 与 authority。Boolean reach extractor 与
ConstraintSolver 共享唯一 Z3 process/result implementation；Boolean DNF 直接由 SAT
assignment vectors 派生，删除无消费者的 `solverTerm`、`solverStatus` 与 solver-version
诊断镜像，但保留 executable 和 composition manifest 的 SHA。当前手写生产 Java 为
68,161 行；快速回归为 69 项并全部通过。

### 全量架构切换：先闭合框架，再集中调试 fixture

接下来的实现不再以原来的巨型类为边界，而只保留五个 domain carrier：

```text
RegionInstancePlan
  {instance, root selector, closure goals}

ClosureGoal
  {kind, admission, execution scope, output closure}

ExecutionTask
  {task identity, selected goal, input actions, replay query}

PathObservation
  {task identity, path condition, branch occurrences, outputs, heap evidence}

RelationSummary
  {producer identity, output closure, guarded cases, admitted edge bindings}
```

JSON 只允许出现在 artifact 读写边界。每个 decoder 保留原始重复 row，用于 exact
cardinality 和冲突检测；进入 domain carrier 后，业务代码不再通过字符串字段反复
`array/object/string/bool`。五个 carrier 之间的转换是单向的，禁止 writer 同时保留旧
Map、禁止 consumer fallback 到上一版 schema。

validation 的唯一 owner 如下：

| 事实 | 唯一 owner | 后续阶段 |
| --- | --- | --- |
| frozen static edge、slice、capture declaration | StaticProgram / Planner boundary | 只引用 canonical ID |
| root、input action、dynamic selector 可执行性 | Scheduler → ExecutionTask | Runtime 直接执行 |
| live object identity、index、event order、replay-local 最后写 | Runtime → PathObservation | Importer 按 task join |
| exact row uniqueness、frame、joint output、heap/Map/array completeness | Importer admission | Worklist 只枚举路径 |
| path coverage 与 guarded merge | Worklist → RelationSummary | Composer 直接消费 |
| cross-region producer selection、read-from equality、SMT sort/expression | Composer | Solver 只求解 |

这意味着：

- `RuntimeRegionPlanner` 删除 activation/base-goal 的 Map 复制，只构造一个
  `RegionInstancePlan`，每个 output demand 只是 `ClosureGoal`；
- `ConcolicScheduler` 不再 deep-copy plan 再删字段，而从 selected goal 一次编译
  `ExecutionTask`；
- `ConcolicRegionRuntime` 删除自己的 container/map selector schema parser，复用唯一
  `DynamicBindingSpec`，并直接产生 `PathObservation`；
- `ConcolicSummaryImporter` 用一个 `ImportedExecution` 和一个保留重复 row 的
  `EvidenceIndex` 完成准入；同一 output/frame/heap extraction 只执行一次；
- `RegionPathWorklist` 只接收 `PathObservation`，branch flip 是内部 `PathQuery`，CLOSED
  时一次生成 `RelationSummary`；
- `ConcolicSmtComposer` 删除已经由 Importer/Worklist 证明过的 dynamic/heap/output
  schema validation，只保留 summary graph、demand fixed point、exact edge join 和 SMT
  emitter。

第一轮全量 cutover 的成功标准不是某个临时行数，而是上述旧 decoder、fallback、
deep-copy-then-strip、第二/第三遍 admission 全部真实删除。预期主要净减来自
Planner/Runtime/Importer/Composer 四个巨型类，而不是把代码移动到新文件。施工期间只要求
全量 compile 和受影响 contract 的聚焦测试；框架闭合并看到千行级净减后，再统一运行
十三个真实 fixture，按 artifact lineage 逐项修复到既定 6 SAT / 7 UNSAT / 0 failure。

### 明确不能删除

必须保留：

- `OutputClosureContract` 及每个 OUT 独立的 output slice；
- capture binding、transformer obligation、container element-field proof；
- joint-output 原子 row 语义；
- `sourceTaskId`/`queryKey` lineage、`dynamicFieldBindings`；
- branch contract、solver path context；
- writer/reader event sequence；
- receiver/value object identity、完整 fingerprint、mutation invocation evidence；
- 唯一 `relationallyComplete`、所有 fail-closed gaps、`CANDIDATE_ONLY`；
- trust-boundary artifact SHA；
- strict symbolic coverage gate，但收敛为 typed `CoverageReport`；
- target exception method 的 branch scope、完整 reached-path PC 与精确 exception-type 筛选。

### 每个 PR 的验收门槛

当前大规模架构重构采用两级门禁。Git 中已经存在最后一个通过全部真实 workload 的
`69439dea` 语义锚点，因此不在每个中间 carrier 修改后等待完整 fixture matrix；先把
下面这条唯一生产链闭合：

```text
RegionInstancePlan
  -> ClosureGoal
  -> ExecutionTask
  -> PathObservation
  -> RelationSummary
  -> composed SMT
```

框架施工阶段的每个 commit 必须满足：

1. ledger 能指出被删字段/代码的 writer 和全部 reader，并说明是零消费者还是由哪个
   canonical value 推导；
2. 生产 Java 净减少；新增类型、codec 或验证必须同时删除更多旧实现，不能只搬代码；
3. 全部生产代码编译通过，并通过直接覆盖当前 cutover 的聚焦 contract 测试；
4. writer、Java reader 和 shell reader 原子切到同一 canonical schema，旧 schema 直接
   拒绝，不保留双写、fallback 或适配层；
5. 不减少 frame、joint-output、heap/Map/array、read-from、branch occurrence、object
   identity、event order、unsupported gap 和 artifact SHA 证据；
6. 新 carrier 必须替换旧 Map/JSON plumbing；如果旧路径尚未删除，这个 commit 不能称为
   framework milestone；
7. 重要框架里程碑独立 commit/push；用户修改的 container fixture 已经明确授权并作为
   `db5a5033` 独立提交，不再作为工作树例外。

当前 framework cutover 已闭合上述 canonical 链。最新大规模删除阶段将手写生产 Java
进一步降到 58,802 行；相对 81,581 行冻结基线累计减少 22,779 行（约 28%），当前
工作批次相对最后安全锚点净减 6,600 余行。快速回归保持为 62 项并全部通过，PMD 不允许
残留 unused private/local/formal/singular-field。这个数字来自真实删除，不包含压格式、
搬文件或删除 correctness evidence。

这一阶段除删除独立 upstream activation、Runtime/Importer 私有 task decoder 和重复
admission/扫描外，还完成了三项一次性切换：

- 删除 `SymbolicRegionAssemblyStage` 及其 `argumentPathFields` 后处理 fixed point；
  `SymbolicRegionPlanner` 直接产生 canonical static region；
- 删除从 Planner、Soot hook、Runtime、Runtime Planner 到 codec 的
  `CALL_ARGUMENT` output capture 整条死路径。所有字段输出只在正常 region exit 从完整
  receiver field path 读取最终 symbolic expression；不同写点、循环 occurrence 和未写
  frame 不再是预先选择的 capture 身份；
- 删除 `captureBindingsComplete`、`captureKind`、raw capture 静态字段副本等镜像；
  唯一准入事实是 `captureBindingIssues.isEmpty()`，旧字段由 V2 codec 直接拒绝，不双写、
  不 fallback。

本批在提交前只运行 Maven compile/test、PMD、diff whitespace 与 shell 语法门禁，明确
没有启动 custom-JDK/Z3 fixture。先完成并推送这一大规模删除里程碑，再进入统一 fixture
调试阶段，避免每删一段旧框架就等待一次昂贵 workload。

正常退出字段捕获的真实 fixture 调试又删除了三条旧假设。第一，完整 root-to-leaf
`fieldPath` 不再与仅含 leaf declaration 的 output cell 路径作错误相等比较；唯一 join 是
同一 execution task 中的 `HEAP_PRESTATE` action、完整 field path 与 exact leaf signature。
第二，跨类 private field 不再由 region root 注入非法 `getfield`，而是在字段声明类生成一个
极小 public static read bridge；primitive 在该 bridge 内装箱，因此 custom VM symbolic
shadow 不会在跨方法返回后丢失。共享父类 root 只有在 activation token 非零时才按
`rootSelector.receiverClass` cast 和读取，未选中的兄弟线程不会执行 output probe。第三，
Importer 对已完整捕获的 scalar/reference `REGION_EXIT_FIELD` 直接使用 normal-exit
expression，不再要求或伪造预选 assignment/write-site coverage；Map/array/container
transformer proof 仍保留原 gate。

提交前真实门禁日志为
`target/robustness-matrix-logs/20260726T022332Z.3255431`：
`completed=13 failures=0`。当前已提交的 container workload 相比历史权威基线增加了
`input4`、将负项移出结果表达式，并把两个正输入夹到 `[10,100]`；因此
`arrayValue ∈ {-1,1}`、`mapValue ∈ {10} ∪ [20,200]`，目标
`arrayValue > mapValue` 正确为 UNSAT。当前矩阵相应为 5 SAT/REACHABLE、8
UNSAT/UNREACHABLE；历史 clean commit 的 6/7 记录保留为当时 fixture 语义，不再作为当前
源码的预期。

当上述 canonical 链端到端闭合后，进入语义调试阶段。此后一次性并行运行全部十三个真实
custom-JDK/Z3 fixture，根据 artifact、path observation、relation summary 和 composition
gap 逐项修复；不能修改 workload 来迎合新框架，也不能用 dry-run/fake Z3。只有恢复完整
基线后，才删除 fixture 证明已经无消费者的最后旧路径并发布最终里程碑：

```bash
GRAPH_CHECKER_MATRIX_JOBS=13 \
  experiments/generic/three-thread-rpc/run_robustness_matrix_parallel.sh all
```

当前预期为五个 `sat/reachable`、八个 `unsat/unreachable`、零 failure。fixture 的
shared-field RPC 模式、一次写/一次读和确定交互顺序不得为了缩短测试而改变。

### 十轮生成式语义回归

大删剪里程碑提交以后，再运行一次性的十轮生成回归。每轮生成十三个 disposable
workload，不修改 `src/test/.../fixtures` 中维护的 workload。每个生成 workload 都沿用同一
RPC contract：两个 producer 各向自己的 primitive shared field 写一次，consumer 按固定
顺序各读一次；producer 完成后才启动 consumer。producer/consumer 内允许固定上界
`for`、组合短路条件、不同字段路径、nested object、array 和 Map，不允许无界循环或用
测试脚本代替程序语义。

生成器先在普通 JVM 上穷举两个 Boolean 输入，确认每轮恰好六个 `REACHABLE`、七个
`UNREACHABLE`；随后才运行真实 custom-JDK、路径闭包、Composer 和 Z3。外层十三个 case
并行，每个 case 的 concolic path worker 也可并行，但 Maven 只构建一次：多个进程不得同时
覆盖共享 `target`。默认命令是：

```bash
GRAPH_CHECKER_GENERATED_JOBS=13 \
CAUSYNTH_GENERATED_CONCOLIC_JOBS=10 \
  experiments/generic/three-thread-rpc/run_generated_round.sh 1
```

轮次参数为 `1..10`。失败日志保存在
`target/generated-regression/logs/round-N/<run-id>/case-XX.log`，对应 case 的 canonical
debug 根目录是 `target/generated-regression/current/case-XX/work`。优先检查
`region_path_manifest.json`、`region_path_worklist.jsonl`、
`concolic_import_diagnostics.jsonl`、merged relation、composition manifest 和最终 SMT。
回归只检查语义 contract、closure 完整性、read-from 顺序和 Z3 结论，不锁定整份 JSON
字节形状，也不恢复已退休字段。修 bug 时应修 canonical producer，而不是在每个 reader
追加 fallback；这正是“不过度校验、不过度设计，同时保障正确性”的执行门槛。

### 最终重构与语义验收（2026-07-26）

大规模删除在 fixture 调试前完成并以 `c78a226b` 推送；生成式回归的第一轮修复以
`8667f21b` 推送。最终手写生产 Java 为 59,039 行，相对 81,581 行冻结基线净减
22,542 行（27.6%）。该数字只统计 `src/main/java/**/*.java`，不靠删除 fixture、压缩
格式或把实现搬到测试目录。

生成式语义回归连续完成十轮，每轮十三个新的 disposable workload，共 130/130 通过。
每轮普通 JVM oracle 都是 6 个 `REACHABLE`、7 个 `UNREACHABLE`，随后真实 custom-JDK
path closure 与 Z3 得到相同结论。第一轮最终日志是
`target/generated-regression/logs/round-1/20260726T062305Z.4075342`；第 2–10 轮由同一
批处理顺序生成、每轮内部 13-way 并行执行。

维护的十三个真实 shared-field RPC workload 也全部通过：当前源码语义为 5 个
`REACHABLE/sat`、8 个 `UNREACHABLE/unsat`。container workload 的两个 producer
worklist 均为 `CLOSED`、`gaps=[]`，Map producer 的 88 个 guarded case 保留 key=7 的
dynamic entry-field binding；最终四个 Boolean valuation 全部 `unsat`。compound-target
的四条 reached path 与 unreachable-compound-target 的空 path set 均由
`CLOSED_IMPORTED_TARGET_REACH_PATH_SET_V1` 产生。最终统一并行门禁为
`completed=13 failures=0`，日志根目录是
`target/robustness-matrix-logs/20260726T072614Z.2098697`。

真实回归暴露并修复的共同 bug 是：runtime-refined output closure 保存了完整
`staticSites`，但 output execution goal 过去只携带 seed path 已观察到的 branch。
短路或早期 branch flip 后首次到达的新 branch 因而有 symbolic PC、却没有 branch
mapping，Importer 只能报 `OUTPUT_REPLAY_REQUIRES_COMPLETE_NORMAL_EXIT`。现在一个
RegionInstance 的 output goal 在第一次 replay 前就携带完整静态 closure 内的 branch
policy；是否被 seed 观察到不再是 output relation 的准入条件。Importer 的完整 normal
exit、exact region-exit capture 和 `relationallyComplete` gate 没有放宽。

同时删除了 robustness shell 中对已退休 `relationships`、root `.cell/.regionId`、
`readyForSolver`、`pathQueryKey` 和 alias-certificate 镜像的逐字段锁定。回归仍检查完整
truth table、SAT/UNSAT、closed worklist、read-from binding、guarded output relation、
dynamic Map/array field binding 和 artifact SHA；不再把诊断 JSON 形状当成第二套语义。

## TODO：用自然 replay 将候选升级为可信结果

当前停止点是准确、结构完整且由 Z3 检查过的候选 SMT。后续工作应把选中的 producer 输入
绑定回真实定义，在完整多线程 workload 中禁止 downstream injection/branch override 地自然
执行，并将唯一 exception annotation target 的实际 observation 与候选 artifact 哈希绑定。
只有该步骤通过后，才可以引入新的 trusted/final trust state；本次改进不实现这一步。
