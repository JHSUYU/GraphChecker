# GraphChecker：region concolic execution 与 SMT composition

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

每个 merge case 保存求解所需的 guard、output/state transformer，以及来源 summary 和
activation 的稳定 id；raw runtime result、完整 activation 和重复 branch trace 不会复制进
merged relation。Merger 只能合并已执行并通过 importer 的 canonical summary；不能把未探索
路径当作不存在。

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
Upstream composer
  -> 沿受证 region edge 将上游 out 绑定到下游 in
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
| `TARGET_BRANCH` | 记录 bug region 的目标 branch | 从一次 unforced observation 得到 solver-ready candidate query；当前不执行 target replay |

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

每个可求解的二元 branch 只产生一个不可变的 typed `BranchWitness`。它包含稳定的
`site + occurrence`、源 execution 实际满足的 outcome/predicate，以及唯一允许的 `VM_PC`
evidence。wire value 本身没有 self-hash；需要稳定去重时，worklist 对 canonical value
计算 key。`BranchReplayContract.flip()` 是唯一可以推导相反 polarity 的位置：它保留有序
prefix、翻转一个 source witness，并丢弃旧 suffix。producer worklist、solver、activation、
静态插桩、runtime、importer 和 verifier 都传递或解析同一个 contract；target 侧只把同一
contract 用作 candidate query，当前 workflow 不执行 target replay。各阶段不再重建旧式
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
activation，不代表程序语义，也不进入稳定 worklist key。

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

## 关键实现

| 组件 | 职责 |
| --- | --- |
| `SymbolicRegionPlanner` | 静态 region、live-in/live-out、output slice 和候选 edge |
| `RuntimeRegionPlanner` / `ConcolicRegionRuntime` | 动态 activation、thread context、精确事件与运行时绑定 |
| `ConcolicScheduler` | 为 target 或 producer 选择 activation 并生成 capture/materialization plan |
| `ConcolicPathFlipPlanner` / `RegionPathWorklist` | pending flip、稳定去重、Z3 输入和 closure |
| `BranchWitness` / `BranchReplayContract` | 二元 branch 的唯一不可变 observation/replay authority |
| `SolverPathContext` | 与 branch authority 分离的、有位置的 typed 非 branch solver constraints |
| `ConcolicPathReplayVerifier` | 用同一 contract 验证有序 witness 流和 input-only replay |
| `ConcolicSummaryImporter` | 将 raw custom-JDK 结果严格导入 `R(in,out)` path summary |
| `RegionSummaryMerger` | 把同一 region 的已验证路径合成 guarded relation |
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

### 不可破坏的语义不变量

任何阶段只有同时满足下列不变量才可删除旧实现：

- 一个 output closure 只包含真实下游 demand 所需的 outputs。
- 每个 output 保留自己的 backward slice、capture/transformer proof 和 completeness；
  output B 的证据不能证明 output A。
- joint output 的所有 capture、PC 和 heap evidence 必须属于同一个原子
  `CONCOLIC_REGION_RESULT` row；row 的 `activationId` 与 producer invocation 共同确定执行
  身份，不再为每个 capture 复制 `executionId`。
- 任一 requested output 缺失、重复、无精确 binding 或不完整时，整个 joint summary
  fail closed；不能生成 partial relation。
- runtime read-from 继续要求 exact region instance、顺序以及适用的 object/value identity。
- worklist 只有在所有 output-relevant 可行 flip 已执行或证明不可行后才可 `CLOSED`。
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
  -> InvocationPlan
  -> ExecutionEvidence
  -> PathCase
  -> RegionRelation
  -> CompositionQuery
  -> SmtProblem
```

JSON 只存在于入口、跨进程交接、持久化和调试导出边界。内部 stage 不直接从任意
`JsonObject` 猜测字段或 fallback；每种 wire schema 只允许一个 decoder/validator。

核心 value 类型包括：

- `MethodRef`、`CellRef`、`FieldRef`、`FieldPath`、`PortRef`、`SiteRef`；
- `StaticRegion`、`OutputSlice`、`OutputMember`、`OutputClosureContract`；
- `Activation`、`MaterializationPlan`、`CapturePlan`、`ExecutionEvidence`；
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
文本；Scheduler 只能把 validated activation 编译成 execution plan；instrumentation 只验证
attestation 并选择 hook。

### Joint multi-output closure

`OUTPUT_CLOSURE` 使用独立、显式版本化的 `outputClosure` envelope。现有
`outputs[]` 只是可由 closure 编译出的 execution action，不再承担 demand schema；
static region、activation、summary、worklist task 也不再靠同名 `outputs` 的形状猜测类型：

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
        "captureBindingsRequired": true,
        "captureBindingsComplete": true,
        "captureBindings": [{
          "captureKind": "FIELD_ASSIGNMENT_RHS",
          "captureBindingId": "REGION.P.out.0.capture.0",
          "outputPort": "REGION.P.out.0",
          "outputCell": "<P: int outX>",
          "method": "<P: void produce()>",
          "siteId": "<P: void produce()>#u4",
          "unitIndex": 4,
          "fieldSignature": "<P: int outX>",
          "occurrence": 1
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
        "captureBindingsRequired": true,
        "captureBindingsComplete": true,
        "captureBindings": [{
          "captureKind": "FIELD_ASSIGNMENT_RHS",
          "captureBindingId": "REGION.P.out.1.capture.0",
          "outputPort": "REGION.P.out.1",
          "outputCell": "<P: int outY>",
          "method": "<P: void produce()>",
          "siteId": "<P: void produce()>#u5",
          "unitIndex": 5,
          "fieldSignature": "<P: int outY>",
          "occurrence": 1
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
完整 slice JSON 作为不可变 defensive copy 保留，因此 field owner、RHS causal edge、
transformer obligation、runtime occurrence 和 object identity 等证据不会在类型化过程中
丢失。

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

首个 writer 切换只允许两个或以上的 member 都有唯一
`CALL_ARGUMENT` / `FIELD_ASSIGNMENT_RHS` 直接 capture，且 JVM descriptor 是 custom JDK
已经支持的 primitive scalar。任一 member 缺 capture、capture 重复或类型不支持，整个 joint
activation fail closed。现有 singleton heap/container/root-return 路径先通过同一 envelope
保留完整 payload 和现有验证，再逐 variant 去掉旧内部适配；不能为了尽快删除 legacy 而降低
这些路径的证明强度。

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

当前一个 raw-result row 本身就是一次 ActiveRegion 的原子 execution envelope；其中的 PC、
heap evidence 和全部 output captures 已由同一 active token 产生，并由 `activationId` 绑定
回唯一计划。Importer 逐 member 验证 capture identity 和完整 demanded keyset 即可，不再为了
重复表达同一事实给每个子 row 增加 `executionId`。只有未来允许一个 row 混合多次 execution
时，才引入新的 execution identity。

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
`demandKey`、`activationId`、`pathKey` 和 `summaryId`；一次 runtime row 的定位仍使用
`activationId` 加 row/content hash，不虚构第二个 execution identity。长期目标 CLI 是：

```text
inspect <artifact>
explain <diagnostic-id>
diff <artifact-a> <artifact-b>
trace <activation-id-or-path-key>
replay <failure-bundle>
```

当前跨进程所需的 execution evidence、summary/relation 和 terminal candidate 继续持久化；
现有 debug formatter 直接读取这些 artifact。`OFF/SUMMARY/FULL` policy、统一 failure
bundle 和上述 inspect CLI 尚未实现，不把它们计作本轮完成项。

### 迁移阶段

当前实施状态（2026-07-24）：

- Phase 0 `COMPLETED`：配置指定的 custom JDK 已完整构建；六个 maintained workload
  已经执行真实 concolic campaign 和真实 Z3，结果为五个 `sat`、一个 `unsat`，没有 skip。
  矩阵使用一次 Maven 构建和六个隔离 workdir 并行执行，shared JAR 在执行前后由 SHA-256
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
  约 61 分钟降到 2 分 49 秒。生产 Java 当前为 81,516 行；相对 84,166 行阶段起点累计
  净减 2,650 行，也比 81,594 行冻结基线少 78 行。除上述 authority cutover 外，已删除
  Replay 派生布尔/计数镜像、Composer 三个零消费者 catalog、Importer 纯 dead helper，
  同时保留原始 failure codes、SMT assertion 和 summary hash。
- 最终源码已从构建、静态分析、runtime planning、完整 producer campaign、
  merge/composition 一直执行到真实 Z3；六个隔离 workload 全并行完成，结果为五个
  `sat/reachable`、一个 `unsat/unreachable`，0 failure，没有用旧 artifact 或增量
  re-compose 代替门禁。最终日志位于
  `target/robustness-matrix-logs/20260724T062900Z.1366357`。custom JDK/`third_party`
  未修改。
- 全量 typed internal pipeline、`ArtifactStore`/inspect CLI、planner 大拆类以及
  45,000–55,000 行宏观目标统一标记为长期 `DEFERRED`，不是本轮正确性里程碑。实测没有
  净简化收益的重写不会为了“完成阶段”而强行加入；若未来重新启动，仍须遵守本节的
  trust-boundary 与六-fixture 门禁。

#### Phase 0：冻结行为与端到端基线

- 记录六个 maintained workload 的 candidate reachability 和直接 Z3 结果。
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
  semantic baseline、boundary regression 和六-fixture 真实 Z3 matrix。
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

# 全部六个 maintained workload
experiments/generic/three-thread-rpc/run_robustness_matrix.sh all

# 推荐：只构建一次，六个 workload 使用隔离目录和日志全部并行
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
- 删除七个仅重复执行 workload main 的 fixture JUnit，但绝不删除或改动六个 maintained
  workload main、配置和实际 Z3 matrix；
- 每批合并或删测前后都运行六 fixture，一直保持五个 `sat`、一个 `unsat`。

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
  只允许来自 canonical output demand，并由 worklist/merge/composition boundary test 与六
  fixture 的真实 Z3 结果共同证明。

### 完成定义

本轮 joint-output authority cutover 与 correctness-preserving cleanup 完成必须同时满足：

- 六个 maintained workload 保持上述五个 `sat` 和一个 `unsat`；
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
代码、关闭具体正确性缺口并通过同一六-fixture 门禁时才重新进入实施计划；单纯拆文件、
搬 JSON 或增加 wrapper 不算进展。

## TODO：用自然 replay 将候选升级为可信结果

当前停止点是准确、结构完整且由 Z3 检查过的候选 SMT。后续工作应把选中的 producer 输入
绑定回真实定义，在完整多线程 workload 中禁止 downstream injection/branch override 地自然
执行，并将唯一 exception annotation target 的实际 observation 与候选 artifact 哈希绑定。
只有该步骤通过后，才可以引入新的 trusted/final trust state；本次改进不实现这一步。
