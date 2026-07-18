# GraphChecker：region concolic execution 与递归 SMT composition

GraphChecker 从静态数据流、运行时跨 region 证据和逐 region concolic execution 中构造
`region.in -> region.out` 关系，再沿 region graph 递归组合成一个可直接交给 Z3 的 SMT。
当前参考工作负载是三线程 RPC fixture；HDFS 实验仍保留为受控的领域实例。

## 第 0 层：项目定位与不可扩展边界

这是一个纯学术的软件工程与程序分析项目，研究静态分析、运行时分析、
concolic execution、symbolic state propagation、guarded symbolic merging 和 SMT
composition。被分析对象是无害的开源 Apache Hadoop HDFS 代码，baseline 工作负载是
HDFS 自有单元测试在本机 `MiniDFSCluster` 中的执行；fresh expiry 实验另使用一个明确
标注为 diagnostic 的本地派生 harness。

`EncryptedTransfer`、encryption key、SASL、token 等词来自 HDFS 上游类名和正常测试
行为，并不表示网络攻击、入侵、利用、漏洞武器化或访问第三方系统。所有 HDFS、
Soot 和自定义 OpenJDK 修改都只用于在受控研究环境中观察和建模程序行为。

固定研究边界如下，脚本也会在每次 HDFS 操作前校验仓库和提交：

| 项目 | 固定值 |
| --- | --- |
| Hadoop 仓库 | `/opt/hadoop` |
| Hadoop commit | `ece33208b89a6a06c1b362d10fab31343fe5df13` |
| HDFS baseline 单测 | `org.apache.hadoop.hdfs.server.balancer.TestBalancerWithEncryptedTransfer#testEncryptedBalancer1` |
| workload | 只使用 `org.apache.hadoop.hdfs.server.balancer.TestBalancerWithEncryptedTransfer#testEncryptedBalancer1` |
| 执行环境 | 本机、Docker 内的自定义 OpenJDK、`MiniDFSCluster` |
| 源码模式 | `UPSTREAM_PRE_HDFS_11741`；循环仅允许由分析器有界/模糊处理，不修改 workload |
| 固定源码 SHA-256 | `be9ce1a57980fdab5612abed1886362842099e1df657b0cdb8c95dbb0a480093` |
| 禁止事项 | 扩展到第三方系统、真实网络目标、攻击或利用工作流 |

任何后续检查点或新对话都必须继续注明上述仓库、commit、唯一 baseline 单测
和执行边界。这里的“固定”是为了保证实验可复现和不越界，不是说分析框架
只能用于 HDFS；核心 concolic/worklist/IR/composer 仍应保持项目无关。

## 当前参考工作负载

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

// Thread 3
int a = getRPCFromA();
int b = getRPCFromB();
if (a > b) throw new BugReachedException(a, b);
```

它使用三个真实 Java worker thread。两个 producer 并发执行并通过 `RpcBus` 发布值；两者
结束后 consumer 才读取值，因此 producer 与 target 的动态 region 不重叠，同时仍保留
真实的跨线程 publish/read 边界。

允许 hard-code 的只有
`experiments/generic/three-thread-rpc/rpc-topology.jsonl` 中的 RPC 方法对应关系。该文件
不包含 `REGION.*` ID、布尔取值、reach condition 或 SMT 文本。region 身份、动态实例、
read-from、branch 和最终公式都必须由分析与执行生成。

当前自动化检查点已经得到：

```text
Producer A: b1 = false -> a = -1
            b1 = true  -> a = 1

Producer B: b2 = false -> b = 10
            b2 = true  -> b = 0

Z3 truth table: 00 unsat, 01 unsat, 10 unsat, 11 sat
reach condition: b1 && b2
```

对应的 bootstrap SMT 和布尔报告由代码自动写入：

```text
target/three-thread-rpc/bootstrap/composed_fatal.smt2
target/three-thread-rpc/bootstrap/bootstrap_boolean_model.json
```

这里的 `BOOTSTRAP` 只表示 SMT 组合和候选输入已得到，不能冒充经过最终自然回放验证的
用户报告。最终自然回放仍是本文末尾的 TODO。

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

### `region.out`

`region.out` 不是“方法返回值列表”，也不是 region 中所有被写过的变量。它只包含会流入
下游 `region.in` 的定义值。返回值、field 写、array 写或传给下游调用的值都可能是 out；
与任何下游 input 无关的临时值不应成为 out。一个 region 可以有多个 output。

静态 dataflow 给出候选 `out -> in` 边；跨线程/RPC 场景允许配置方法级拓扑，但最终边仍
需要具体 runtime publish/read、顺序和对象/值证据确认。

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
Soot 静态分析
  -> region.in/out、output slice、候选 region edges
运行时 discovery trace
  -> activation、thread context、branch event、精确 read-from
Scheduler
  -> 为一个 target 或一个 producer region 生成 capture plan
逐 region concolic campaign
  -> seed -> pending path flip -> Z3 input -> custom-JDK replay -> strict import
Guarded merge
  -> 每个 producer 的 R_region(in, out)
Recursive composer
  -> 上游 out 绑定下游 in，递归接入 target condition
Z3
  -> composed SMT、truth table、候选 reach condition
自然传播验证
  -> TODO
```

### 两种 capture goal

| Goal | 用途 | 闭合条件 |
| --- | --- | --- |
| `OUTPUT_CLOSURE` | 学习 producer 的输入到输出关系 | 所有 output-relevant 可行路径已执行，worklist 无 pending |
| `TARGET_BRANCH` | 记录 bug region 的目标 branch | 获得精确 target condition；最终必须由无注入自然回放验证 |

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
pending = 0  ->  COMPLETE_BOUNDED_PATH_CLOSURE
```

随后才允许生成 guarded relation。这样不会在已经观察到 branch 两侧后再产生无意义的
反向 replay。

## Runtime 与 custom JDK

Scheduler 为每次 capture 选择一个 region activation。GraphChecker runtime 维护 token 化
的 region/thread context；custom JDK 使用 thread-local concolic context，并限制同一时刻的
engine-backed owner，避免其他应用线程或 GraphChecker 自身 bookkeeping 污染当前 path
condition。

Branch 身份由 VM 观察到的 `site + occurrence + outcome` 绑定，而不是靠不稳定的全局
branch 序号猜测。这里的 invocation ordinal 只表示同一 receiver-class/thread context 中的
第几次调用，用于定位动态 activation，不代表程序语义，也不进入稳定 worklist key。

Producer 的模型只能 materialize 到静态分析找到并由 instrumentation 确认的真实定义位置。
`forcedBranches` 不能作为关系证据。最终 target replay 必须是 observation-only：不得给
consumer 注入 model、返回值或 branch outcome。

## 递归 SMT composition

Composer 从 fatal query 反向遍历 region graph。若下游端口 `D.in.j` 由上游端口
`P.out.k` 提供，它会建立受证绑定，并把 `R_P` 接入 `R_D`。若 `P.in` 仍来自其他 region，
相同步骤继续递归；root input 才保留为最终 SMT 的自由输入。

对三线程 workload，组合语义等价于：

```text
a = ite(b1, 1, -1)
b = ite(b2, 0, 10)
bug = (a > b)
```

但这些文本没有 hard-code 在 workflow 中；它们来自四条 producer path summary、两条
runtime-confirmed RPC edge 和 target branch condition。最终 SMT 由
`ConcolicSmtComposer` 生成，`BooleanReachConditionExtractor` 再对自动发现的 Java Boolean
root 做有限真值表投影并生成 canonical DNF。

Composer 采用 fail-closed 规则：缺 summary、未闭合 relation、未绑定端口、unsupported
expression、来源不唯一或 target 未验证时，只能产生 bootstrap/incomplete manifest，
不能发布 final relationship。

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
身份一致。

领域 adapter 只能提供候选映射，不能补写程序没有执行出来的 equality、cache、expiry、
membership 或 codec 语义。缺失证据必须保留为 gap。

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

`all` 串联 build、static analysis、trace、discovery、target seed、producer campaigns、
bootstrap composition、projection、natural replay、final composition。当前实现会在下面的
自然回放 TODO 完成前停止，不能期待已生成 `final/boolean_reach_condition.json`。

## 关键实现

| 组件 | 职责 |
| --- | --- |
| `SymbolicRegionPlanner` | 静态 region、live-in/live-out、output slice 和候选 edge |
| `RuntimeRegionPlanner` / `ConcolicRegionRuntime` | 动态 activation、thread context、精确事件与运行时绑定 |
| `ConcolicScheduler` | 为 target 或 producer 选择 activation 并生成 capture/materialization plan |
| `ConcolicPathFlipPlanner` / `RegionPathWorklist` | pending flip、稳定去重、Z3 输入和 closure |
| `ConcolicPathReplayVerifier` | 验证 replay prefix、目标 outcome 和无 branch override |
| `ConcolicSummaryImporter` | 将 raw custom-JDK 结果严格导入 `R(in,out)` path summary |
| `RegionSummaryMerger` | 把同一 region 的已验证路径合成 guarded relation |
| `ConcolicSmtComposer` | 递归绑定上游 out 与下游 in，生成 composed SMT |
| `BooleanReachConditionExtractor` | 调用 Z3 枚举 Boolean roots 并生成 reach condition |
| `ConcolicPrimitiveBootstrapProjector` | 把 SAT case 投影回 producer 的真实输入动作 |
| `ConcolicNaturalReplayValidator` | 检查最终自然传播；当前三线程集成仍为 TODO |
| `run_engine.sh` | 配置驱动的通用阶段编排 |

custom JDK 位于 `third_party/OpenJDK-Concolic-Execution-Engine`。三线程端到端 fixture、拓扑、
配置和阶段脚本位于 `experiments/generic/three-thread-rpc`。

## TODO：最终自然回放验证

当前唯一保留在主流程上的 TODO 是把 bootstrap 候选变成最终的自然传播证据：

1. 将 Z3 选中的 `b1=true`、`b2=true` 精确绑定到 producer activation 的真实定义动作；
   instrumentation 已找到 definition site 时，必须把 deferred plan 解析并持久化为可 replay
   的权威 action。
2. 生成一个 `ALL` replay bundle：两个 producer 只接收各自的 input assignment；consumer
   保持 engine-backed、observation-only，且 model assignment、return materialization 和
   forced branch 数量都为零。
3. 在 custom JDK 上运行三个真实线程，验证 producer 自然产生 `a=1`、`b=0`，RPC 自然
   传播这两个值，consumer 自然观察到 `a > b` 和 `BugReachedException`。
4. strict importer 与 natural replay validator 绑定同一 activation、region instance、branch
   site/occurrence 和异常证据。
5. 只有上述验证通过后，重新生成 `VALIDATED_FINAL` SMT、relationship proof 和最终
   `target/three-thread-rpc/final/boolean_reach_condition.json`。

在此 TODO 完成之前，可以准确声称“SMT 与候选条件已全自动生成并由 Z3 求解”，但不能
声称最终 reach condition 已通过自然传播验证。
