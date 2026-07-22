# GraphChecker：region concolic execution 与递归 SMT composition

GraphChecker 从静态数据流、运行时跨 region 证据和逐 region concolic execution 中构造
`region.in -> region.out` 关系，再沿 region graph 递归组合成一个可直接交给 Z3 的 SMT。
当前维护的验证矩阵是通用三线程 RPC fixture 及其 cross-method、multitype、
dependent-scalar、container、unreachable-parity 变体。最后一组要求完整流程生成的
SMT 由 Z3 判定为 `unsat`。

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
保持 existential）。终态 manifest 明确写为
`COMPLETE_Z3_CHECKED_CANDIDATE / CANDIDATE_ONLY`；它绑定 SMT、composition manifest、
reach model 和 relationship candidates 的路径、大小及 SHA-256，但不会声称已经得到可信最终
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

对应的 candidate SMT、composition manifest 和布尔模型由代码自动写入：

```text
target/three-thread-rpc/candidate/candidate.smt2
target/three-thread-rpc/candidate/candidate_composition_manifest.json
target/three-thread-rpc/candidate/candidate_boolean_model.json
```

这些 artifact 只表示 candidate composition 已完成且 Z3 已检查，不能冒充经过最终自然回放
验证的用户报告。`run.sh all` 最终生成
`target/three-thread-rpc/candidate/candidate_result_manifest.json`，其中
`naturalReplayPromotionImplemented=false`。

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

每个 case 都保留其原始 summary、activation、branch trace 和 concrete observation。Merger
只能合并已执行并通过严格 importer 的 case；不能把未探索路径当作不存在。

## 自动分析流程

```text
classfile exception annotation
  -> 唯一 target NEW/method/Jimple throw
Soot annotation-directed 静态分析
  -> 从 target 反向得到 region.in/out、output slice、候选 region edges
运行时 discovery trace
  -> activation、thread context、branch event、精确 read-from
Scheduler
  -> 为一个 target 或一个 producer region 生成 capture plan
逐 region concolic campaign
  -> seed -> pending path flip -> Z3 input -> custom-JDK replay -> strict import
Guarded merge
  -> 每个 producer 的 R_region(in, out)
Recursive composer
  -> 上游 out 绑定下游 in，递归生成 candidate composition
Z3
  -> candidate SMT、Boolean truth table、候选 reach condition
Candidate manifest
  -> hash-bind SMT、composition、reach model 和 relationship candidates
TODO: 自然传播可信升级
  -> SAT 输入自然 replay；绑定实际 target exception 后才能发布可信结果
```

### 两种 capture goal

| Goal | 用途 | 闭合条件 |
| --- | --- | --- |
| `OUTPUT_CLOSURE` | 学习 producer 的输入到输出关系 | 所有 output-relevant 可行路径已执行，worklist 无 pending |
| `TARGET_BRANCH` | 记录 bug region 的目标 branch | 获得候选 target condition；可信升级留待自然 replay TODO |

Producer campaign 不需要一次让 custom JDK 同时符号执行三个线程。系统一次选择一个
region activation，多跑若干次 workload，分别学出每个 `R_region`；跨 region 关系在
composer 中组合。

### `pending` 与 campaign

`pending` 不是 Z3 的 `unknown`，也不是尚未启动的线程。它是一项尚未被真实 execution
覆盖的 branch-flip 任务，身份包含 requested output、路径 prefix、branch site、occurrence、
目标 outcome 和 runtime bindings。

一次 execution 会加入一条 observed path。若该 trace 已自然覆盖某个 flip 的目标
frontier，该任务直接视为 covered；否则 planner 才让 Z3 求一个新输入并 replay。不同
prefix 下的同一 branch 仍是不同任务。campaign 重复这个过程，直到：

```text
observed paths > 0 && pending = 0 && gaps = []  ->  state = CLOSED
```

没有 output-closure seed 时 manifest 显式报告 `state = NOT_STARTED` 和 gap；不能把
零条 observed path 或缺失 manifest 当成 closed。只有 `CLOSED` 才允许生成 guarded
relation。这样不会在已经观察到 branch 两侧后再产生无意义的反向 replay。

## Runtime 与 custom JDK

Scheduler 为每次 capture 选择一个 region activation。GraphChecker runtime 维护 token 化
的 region/thread context；custom JDK 使用 thread-local concolic context，并限制同一时刻的
engine-backed owner，避免其他应用线程或 GraphChecker 自身 bookkeeping 污染当前 path
condition。

每个可求解的二元 branch 只产生一个不可变、内容哈希的 `BranchWitness`。它包含稳定的
`site + occurrence`、源 execution 实际满足的 outcome/predicate，以及唯一允许的 `VM_PC`
evidence。`BranchReplayContract.flip()` 是唯一可以推导相反 polarity 的位置：它保留有序
prefix、翻转一个 source witness，并丢弃旧 suffix。worklist、solver、activation、静态插桩、
runtime、importer 和 verifier 都传递或解析同一个 contract，不再各自重建 `targetBranch`、
`expectedBranchPrefix`、negated condition 或 scheduled-target 副本。精确 VM event 若没有
对应 PC，只能作为 observation 和诊断信息，不能制造 predicate、witness 或 flip；`switch`
也仍是独立的 successor-aware observation，不伪装成二元 branch。

源 path condition 中夹在 branch 之间的 array-load 或 method-relation 节点不是 branch
evidence。schema-3 worklist 把它们放入另一个不可变、内容哈希的 `SolverPathContext`，并保留
原始 `summaryPcIndex`；该对象只接受 `_array_expr` 和 `MethodExpression`，遇到没有 witness
的 Boolean predicate 会直接拒绝。solver 分别断言 context 与 contract，runtime replay 只
消费 contract。这样既不会丢掉求解所需的非 branch 关系，也不会再把同一个 branch witness
复制成多套 path-condition/target/prefix JSON 来相互确认。

invocation ordinal 只表示同一 receiver-class/thread context 中的第几次调用，用于定位动态
activation，不代表程序语义，也不进入稳定 worklist key。

跨 RPC/codec/SASL 的值传播使用独立的 runtime-confirmed `EQUALITY` binding：它要求两端
canonical port、exact region instance、完整 value fingerprint 和 writer-before-reader 顺序，
但不要求序列化前后的对象 identity。它与共享 field 的 `READ_FROM` 保持不同 relation kind，
composer 按 edge、kind、instance 和 runtime witness 精确选择，二者不能互相替代。

Producer 的模型只能 materialize 到静态分析找到并由 instrumentation 确认的真实定义位置。
`forcedBranches` 不能作为关系证据。当前输出到候选模型为止；未来的可信升级必须让 target
保持 observation-only，不得给 consumer 注入 model、返回值或 branch outcome。

Map 变异只通过 VM `MethodExpression` 导入通用的 `MAP_PUT` / `MAP_REMOVE` /
`MAP_CLEAR` / `MAP_PUT_ALL` heap transformer。直接 `Map.remove(key)` 受支持；maintained
contract 刻意不支持 `Iterator.remove()` 变异：精确 static causal-edge `invoke` 可以识别该
调用，但 VM `HashMap.removeNode` 证据无法证明对应的 application call 与 current entry。
importer 因此报告 `INCOMPLETE_ITERATOR_REMOVE_APPLICATION_PROVENANCE`，并令
`heapEffectModel.complete=false`、`relationallyComplete=false`，而不是通过 side channel
猜测 backing map/key 或生成不可信 SMT。iterator `next()`、entry/key/value 读取、有限 Map
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

Manifest 中的来源检查不是密码学“证书系统”，而是防止把不同 execution、旧 summary 或
merged relation 内部的错误 case 拼在一起。核心规则是：选中的 case 必须唯一属于本次
composer 实际使用的 merged summary，同时其原始 summary 和 activation 必须唯一存在且
身份一致。branch 层的检查以 `BranchWitness`/`BranchReplayContract` 的 canonical JSON 与
content hash 为准；下游只解析并消费该权威对象，不再逐字段重建一份“等价证书”。

Composition manifest 是跨文件绑定的唯一 authority：它对本次 CLI 实际读取的 regions、
fatal query、summary、生成的 SMT 和 relationship catalog 做精确路径、长度和 SHA-256
绑定。relationship catalog 只保存 schema、候选关系数组和当前 verification eligibility，
不再复制 fatal identity、stage、artifact hash 或第二个 `compositionBindingId` 来与 manifest
逐字段互证。

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

## 关键实现

| 组件 | 职责 |
| --- | --- |
| `SymbolicRegionPlanner` | 静态 region、live-in/live-out、output slice 和候选 edge |
| `RuntimeRegionPlanner` / `ConcolicRegionRuntime` | 动态 activation、thread context、精确事件与运行时绑定 |
| `ConcolicScheduler` | 为 target 或 producer 选择 activation 并生成 capture/materialization plan |
| `ConcolicPathFlipPlanner` / `RegionPathWorklist` | pending flip、稳定去重、Z3 输入和 closure |
| `BranchWitness` / `BranchReplayContract` | 二元 branch 的唯一不可变 observation/replay authority |
| `SolverPathContext` | 与 branch authority 分离的、有位置且内容哈希的非 branch solver constraints |
| `ConcolicPathReplayVerifier` | 用同一 contract 验证有序 witness 流和 input-only replay |
| `ConcolicSummaryImporter` | 将 raw custom-JDK 结果严格导入 `R(in,out)` path summary |
| `RegionSummaryMerger` | 把同一 region 的已验证路径合成 guarded relation |
| `ConcolicSmtComposer` | 递归绑定上游 out 与下游 in，生成 composed SMT |
| `BooleanReachConditionExtractor` | 调用 Z3 枚举 Boolean roots 并生成 reach condition |
| `run_engine.sh` | 配置驱动的通用阶段编排 |

custom JDK 位于 `third_party/OpenJDK-Concolic-Execution-Engine`。三线程端到端 fixture、拓扑、
配置和阶段脚本位于 `experiments/generic/three-thread-rpc`。

## TODO：用自然 replay 将候选升级为可信结果

当前停止点是准确、结构完整且由 Z3 检查过的候选 SMT。后续工作应把选中的 producer 输入
绑定回真实定义，在完整多线程 workload 中禁止 downstream injection/branch override 地自然
执行，并将唯一 exception annotation target 的实际 observation 与候选 artifact 哈希绑定。
只有该步骤通过后，才可以引入新的 trusted/final trust state；本次改进不实现这一步。
