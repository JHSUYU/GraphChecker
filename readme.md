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
| `TARGET_BRANCH` | 学习目标异常所在 consumer function 的到达条件 | 所有 target-function branch 的可行路径已执行，worklist 无 pending |

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

一条路径上的 output-relevant branch 可能因为更早的约束而被 VM concretize。此时它没有
可翻转 predicate，但也不能在仍有 pending bridge task 时立刻终止 campaign。worklist 先把
它记为 `deferredObservations`；后续只有相同 output closure、相同 site 且相同 occurrence
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

这个规则只用于 `TARGET_BRANCH`。producer output slice 仍使用原有控制依赖规则，避免扩大
output closure。运行时从一次未强制 seed 开始，只翻转 target activation 中实际出现的
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
`stderr.log`、task 目录中的 `hs_err_pid*.log` 和 replay activation 仍足以定位执行阶段。
成功 wave 会按既有 policy 清理，失败 wave 始终保留。

## Runtime 与 custom JDK

Scheduler 为每次 capture 选择一个 region activation。GraphChecker runtime 维护 token 化
的 region/thread context；custom JDK 使用 thread-local concolic context，并限制同一时刻的
engine-backed owner，避免其他应用线程或 GraphChecker 自身 bookkeeping 污染当前 path
condition。

每个可求解的二元 branch 只产生一个不可变的 typed `BranchWitness`。它包含稳定的
`site + occurrence`、源 execution 实际满足的 outcome/predicate，以及唯一允许的 `VM_PC`
evidence。wire value 本身没有 self-hash；需要稳定去重时，worklist 对 canonical value
计算 key。`BranchReplayContract.flip()` 是唯一可以推导相反 polarity 的位置：它保留有序
prefix、翻转一个 source witness，并丢弃旧 suffix。producer/target worklist、solver、
activation、静态插桩、runtime、importer 和 verifier 都传递或解析同一个 contract；target
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
| `RuntimeRegionPlanner` / `ConcolicRegionRuntime` | 动态 activation、thread context、精确事件与运行时绑定 |
| `ConcolicScheduler` | 为 target 或 producer 选择 activation 并生成 capture/materialization plan |
| `ConcolicPathFlipPlanner` / `RegionPathWorklist` | 纯 frontier planning、pending flip、稳定去重和 closure |
| `ConcolicPathFlipSolver` | 精确求解一个 query，生成 singleton replay activation |
| `BranchWitness` / `BranchReplayContract` | 二元 branch 的唯一不可变 observation/replay authority |
| `SolverPathContext` | 与 branch authority 分离的、有位置的 typed 非 branch solver constraints |
| `BranchReplayObservationValidator` | 在 runtime 与 Importer 边界验证有序 witness 流 |
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

#### Worklist、Merger、Composer

核查并删除：

- `ConcolicSmtComposer.MergeStats`
- worklist task 的固定 `status=PENDING_SOLVE`
- `dynamicIdsExcludedFromQueryKey`
- 可由 closure/activation 推导的 `rootMethod`
- 顶层 `regionInstanceId/rootCallId/outputDemandKey/outputClosureFingerprint` 镜像
- 无消费者的顶层 `engineArrayInputBindings`
- `caseProjectionCatalogComplete`
- relationship 的固定 `status=UNVERIFIED_CANDIDATE`

从 `RegionSummaryMerger` 核查并删除可由 canonical 数组、`gaps`、`kind/schema` 推导的：

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

### 明确不能删除

必须保留：

- `OutputClosureContract` 及每个 OUT 独立的 output slice；
- capture binding、transformer obligation、container element-field proof；
- joint-output 原子 row 语义；
- `sourceActivationId`、`dynamicFieldBindings`；
- branch contract、solver path context；
- writer/reader event sequence；
- receiver/value object identity、完整 fingerprint、mutation invocation evidence；
- 唯一 `relationallyComplete`、所有 fail-closed gaps、`CANDIDATE_ONLY`；
- trust-boundary artifact SHA；
- strict symbolic coverage gate，但收敛为 typed `CoverageReport`；
- target exception method 的 branch scope、完整 reached-path PC 与精确 exception-type 筛选。

### 每个 PR 的验收门槛

每个 PR 必须同时满足：

1. ledger 能指出被删字段/代码的 writer 和全部 reader，并说明是零消费者还是由哪个
   canonical value 推导；
2. 生产 Java 净减少；新增类型、codec 或验证必须同时删除更多旧实现，不能只搬代码；
3. 当前 13 类 / 57 项快速回归通过，不新增锁定整份 JSON 的测试；
4. 受影响的 fixture 运行真实 concolic 与真实 Z3，不用 dry-run/fake Z3；
5. schema 切换同时更新 writer、Java reader、shell reader，旧 schema fail closed；
6. SAT/UNSAT、root sorts、joint-output case、read-from 与 target-path 语义不漂移；
7. 不减少 unsupported/gap coverage，不用 fallback 或自由符号换取“成功”；
8. 重要里程碑独立 commit/push。

删除旧 authority 或完成一个 schema cutover 前，必须运行全部十三个 fixture：

```bash
GRAPH_CHECKER_MATRIX_JOBS=13 \
  experiments/generic/three-thread-rpc/run_robustness_matrix_parallel.sh all
```

预期仍为六个 `sat/reachable`、七个 `unsat/unreachable`、零 failure。fixture 的 shared-field
RPC 模式、一次写/一次读和确定交互顺序不得为了缩短测试而改变。

## TODO：用自然 replay 将候选升级为可信结果

当前停止点是准确、结构完整且由 Z3 检查过的候选 SMT。后续工作应把选中的 producer 输入
绑定回真实定义，在完整多线程 workload 中禁止 downstream injection/branch override 地自然
执行，并将唯一 exception annotation target 的实际 observation 与候选 artifact 哈希绑定。
只有该步骤通过后，才可以引入新的 trusted/final trust state；本次改进不实现这一步。
