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

### HDFS-11741 通用递归 composition → fatal SMT checkpoint（2026-07-18）

Hadoop worktree 保持 pre-fix commit，baseline test 未修改。v4 静态 catalog 和唯一一次
baseline workload 的 runtime trace 已冻结；后续步骤直接复用这些产物，不再重复运行 Soot、
runtime instrumentation 或 workload。输入路径、summary 列表、输出文件名、Z3 路径和语义
policy 均由 `experiments/hdfs/conf/hdfs.properties` 配置，并可用对应的
`CAUSYNTH_HDFS_GENERIC_*` 环境变量覆盖。配置中没有生成的 activation/region ID。

正式结果位于 `target/hdfs-11741-generic-final-v7`。这条路径不再调用
`Hdfs11741BootstrapComposer`，也没有注入面向本 bug 的 case formula：HDFS-specific 部分只负责
按 method/cell/timeline policy 选择语义角色以及提供已声明的 RPC/SASL mapping；之后由 legacy
branch-flip scheduler 和普通 `ConcolicSmtComposer` 完成 target fatal PC、递归 port binding、
summary symbolic merging、SMT emission 和 Z3 调用。solver manifest 对此记录为
`domainSemanticAdapterUsed=false`、`caseFormulaInjected=false`。

当前自动化证据链如下：

- selector 从 frozen catalog 自动选出 NameNode、DataNode、KeyUpdater、Dispatcher 和 target
  五个有序语义角色。它依据 root/anchor/required method、requested cell、runtime instance
  顺序和完整值 fingerprint 选择，不依赖某次生成的 activation/region 名字；
- exact composition 包含四个 producer summary：NameNode、DataNode、KeyUpdater 和
  Dispatcher。target replay summary 由 scheduler 单独消费，用来翻转最后的 `key == null`
  fatal branch，因此不重复列在 composition manifest 的 `includedSummaries` 中；
- composer 从 target input port 出发，沿 frozen runtime binding catalog 递归解析唯一 producer。
  当前三条 exact binding 分别覆盖 Dispatcher→target 的 SASL username 值相等、DataNode
  `allKeys` post-state→target lookup map 的 shared-field read-from，以及
  KeyUpdater `currentKey`→Dispatcher cache input 的 declared-field projection。Dispatcher
  summary 内部另用 exact equality-preserving causal path 证明 cached keyId 与生成的
  `DataEncryptionKey.keyId` 相等；Java int→decimal string→parse-int round trip 由通用 String
  codec 语义翻译，而不是 HDFS case formula；
- NameNode→KeyUpdater/DataNode 的 RPC payload 在现有 frozen trace 中没有完整 transaction
  fingerprint，所以这两条边使用 policy 中显式声明、selector 自动解析的配置化 field mapping。
  policy 只写稳定 role/port alias/cell/field path，不写 ACT/REGION ID；selector 将其解析到本次
  runtime instance，通用 composer 再把 equality group 展开为三个有类型约束：NameNode
  `MAP_PUT.keyExpression` 分别等于 KeyUpdater `currentKey.keyId` 和 DataNode iterator
  `keyId`，NameNode `expiryDate` 等于 DataNode entry `expiryDate`。manifest 记录
  `configuredTransportProducerCount=1`、`configuredTransportBindingCount=2`、
  `configuredTransportConstraintCount=3`。这是可见的 `CONFIGURED_NN_SNAPSHOT_FANOUT`
  approximation，不是 domain composer 注入的整段 bug formula。NameNode source 采用 manifest
  可审计的 `GUARDS_AND_SELECTED_TERMS_ONLY` projection：保留 source path guards 和被选中的
  payload terms，但不声称已经构造完整 heap transformer；
- DataNode summary 对内层 `removeExpiredKeys()` iterator 保留一个相关 map entry：
  `expiry < Time.now() -> remove(keyId)`。composer 将 exact post-state edge 与 fatal
  `Map.get(keyId) == null`、删除前 membership 和 `MAP_REMOVE` store semantics 组合起来；base SMT
  没有直接断言“removed key = fatal lookup key”，该相等关系是由 pre-present、post-absent 和
  remove transformer 推出的。对正式 SMT 额外断言这个派生等式的否定，Z3 返回 `unsat`；再
  强制 NameNode snapshot key 与 fatal lookup key 不同也返回 `unsat`，说明配置化 fanout、
  KeyUpdater/Dispatcher/SASL codec 和 DataNode remove 两条链已在同一模型中汇合；
- NameNode projection summary 保留其初始 guard `snapshotExpiry >= NameNode Time.now()`；DataNode
  summary 保留稍后 `snapshotExpiry < DataNode Time.now()`，所以同一 SMT 明确得到时间跨越。
  外层 NameNode heartbeat 与 DataNode `BPServiceActor.run` 长循环只保留配置声明的有界
  witness/path prefix，DataNode iterator 只展开上述一个相关 entry。一个与 fatal `allKeys`
  无关的 ancillary computed map key 保留为 typed opaque concrete-workload result；这些都是
  manifest 可见的 approximation，而不是 sound/complete 的全 HDFS 循环模型；
- 正式 composition 状态为 `STRUCTURALLY_COMPLETE_BOOTSTRAP_COMPOSITION`：
  `structurallyComplete=true`、`eligibleForBootstrapModel=true`，并且
  `missingSummaryRegions`、`incompleteSummaryRegions`、`unsupportedExpressions`、
  `unboundPorts` 均为空。Z3 4.8.12 已真实运行并返回 `sat`；
- `complete=false` 只表示这个 solver model 尚未经过一次自然 fatal replay 验证，不表示当前
  summary→binding→SMT 结构缺失。它证明的是声明的一 DN、单相关 iterator entry 和有界外层
  loop scope 下存在到达 `retrieveDataEncryptionKey()` 中 `key == null` exception branch 的模型。

冻结的静态图仍有 150,000 条边、64 个 region 和 8,728 条 region edge；唯一 workload
运行 56.856 秒并通过，raw trace 有 839,101 行且 streaming manifest 为
`CLOSED/complete`。最终 offline aggregation 有 499 个 activation 和 57 条 confirmed
read-from edge。这些较大的分析步骤不是下面一键 composition 命令的一部分。

正式 artifact 为：

```text
target/hdfs-11741-generic-final-v7/
  semantic-selection/replay_selection_manifest.json
  directed-target-query/branch_queries.jsonl
  hdfs_11741_generic.smt2
  hdfs_11741_generic_manifest.json
  hdfs_11741_generic_relationships.json
  hdfs_11741_generic_z3.out
  hdfs_11741_generic_z3_manifest.json
```

其中 composition manifest、SMT 和 solver output 的 SHA-256 分别为
`5ad1029f26572691e4c286209ce93152375ccf438681c6e2d2d35b9fa2a764bd`、
`5b58bc1a2e1f68ce28f479771b370a218e9a28ca983990da10fe4b314236e786`、
`d9dbf94b05b8314af9ca7f2034e92685c33447917605a7243b1099c693a12e5e`。

从配置指定的 frozen artifacts 一键重现 selector→fatal flip→generic composition→Z3：

```bash
mvn -q -DskipTests package
CAUSYNTH_HDFS_GENERIC_OUTPUT_DIR=/opt/GraphChecker/target/hdfs-11741-generic-fresh \
  experiments/hdfs/run_hdfs.sh hdfs-11741-compose-generic \
  org.apache.hadoop.hdfs.server.balancer.TestBalancerWithEncryptedTransfer#testEncryptedBalancer1
```

输出目录必须尚不存在且位于 workspace 内，以保证并行 worker/重复实验彼此隔离。除新的输出
目录外，命令所需路径和文件名均读取 properties；如需搬迁 frozen artifacts，应修改配置或
使用同名 `CAUSYNTH_HDFS_GENERIC_*` override，而不是修改脚本或写入生成的 ID。

派生 key 关系可从 relationships artifact 自动取出并做独立反证检查；下面命令在正式 SMT
末尾加入关系的否定，预期输出 `unsat`：

```bash
artifact=/opt/GraphChecker/target/hdfs-11741-generic-final-v7
derived_relation=$(jq -r \
  '.relationships[] | select(.kind == "DERIVED_MAP_REMOVE_FATAL_MISS_KEY_EQUALITY") | .formula' \
  "$artifact/hdfs_11741_generic_relationships.json")
{
  sed '$d' "$artifact/hdfs_11741_generic.smt2"
  printf '(assert (not %s))\n(check-sat)\n' "$derived_relation"
} | /usr/bin/z3 -in -smt2
```

#### Activation-specific concolic 静态复用

纯 concolic replay class generation 不再为每个 activation 重建同一份 150,000-edge
静态图。`freeze-concolic-static` 会把 regions、coverage、static graph、region edges、
target spec、原始 class tree 和 supplemental class tree 绑定到一个只读 manifest；loader
再用同目录的 schema-2 `schedule_input_provenance.json` 校验 exact plan、regions 和 graph
SHA。冻结前还会强制 static-process provenance 中的 Hadoop source revision、target-spec
路径/SHA 和 class-tree 路径完全一致。每个 worker 只流式投影所选 region 的 `methods` 与
`branchPolicies`，继续复用原有 root/materialization/replay/output-capture instrumentation。

真实 `ACT.30 / REGION.0` 测量中，原先完整静态重建约需 1,428 秒；复用模式的
GraphChecker pass 稳定在 30.9–31.2 秒，包含 runtime dependency 发布的完整
`process-concolic` 为 34–35 秒。所选 1 个 root、9 个 branch policy 全部安装，报告记录
`staticAnalysisSkipped=true`，约为 42 倍的端到端加速。固定 regex 也已在静态/运行时
region planner 热路径预编译。`trace+concolic` campaign 和 `ALL` bundle 暂不使用 partial
catalog，会明确回退完整分析。

本次优化后完整回归为 675 项 JUnit 零失败；generic workflow、三线程 RPC JUnit fixture 和
parallel HDFS concolic batch fixture 也全部通过。

```bash
mvn -q -DskipTests package
experiments/hdfs/run_hdfs.sh freeze-concolic-static
experiments/hdfs/run_hdfs.sh process-concolic \
  /path/to/scheduled_activation_plan.jsonl ACT.id
```

成功的 fast process 只在 job-owned static output 中写
`concolic_instrumentation_report.json` 和 `concolic_process_provenance.json`；不会调用
partial `OutputWriter.writeAll()`，因此不会用空 graph/plan 覆盖冻结 catalog。manifest、
artifact 文件名、输出目录和 Java/`jar` 命令均由 properties 或环境变量配置。process
provenance 还绑定最终 replay class tree 的确定性 SHA-256 与 file count；batch runner 和
exact reuse `replay-concolic` 会在启动 custom JDK 前重新计算 class tree，并复核 manifest、
instrumentation report、GraphChecker JAR 的路径/SHA 和 authority，缺失 provenance 时直接
拒绝运行。显式 full-static/legacy replay 可设置
`CAUSYNTH_CONCOLIC_PROCESS_PROVENANCE_REQUIRED=false`；也可单独运行
`verify-concolic-process` 审计。实际 instrumentation root 必须属于所选 region 的 method
catalog，并与 pipeline 安装的唯一 root 精确相等；supplemental process dirs 保留 Soot
classpath 顺序并拒绝重复。可删除的 class output 只允许 checked-in exact path、专用
replay root 的严格子目录，或 batch/campaign 已校验后显式授权的 exact job path。

#### 三线程自然 replay milestone（2026-07-18）

README 的三线程 RPC 工作流现已完整跑通，不再停在 bootstrap 候选模型。scheduler 在
`CALL_RETURN` 或 `REGION_LIVE_IN` 由权威静态 DefinitionIndex 唯一解析到 primitive local
定义点后，会解除早期 `deferredResolution` 状态并保留 discharge authority；零个或多个
定义点仍保持 unresolved。projector 接受这两种来源的唯一
`STATIC_DATAFLOW_DEF_SITE`，仍拒绝 deferred action、缺失 source binding 或不一致的
method/local/site identity。

Z3 选择 `b1=true, b2=true` 后，projector 生成 2 个 producer replay 和 1 个
observation-only target replay 的三行 `ALL` bundle。custom JDK 自然产生 `a=1, b=0`，经
RPC/shared field 传播后由 consumer 自然触发 `BugReachedException`；没有 forced branch、
target model assignment 或 reference-result injection。最终 composition、relationship proof
和 exhaustive Boolean projection 均通过，得到：

```text
(and (= sym__port__REGION_1_in_0__int 1)
     (= sym__port__REGION_2_in_0__int 1))
```

bootstrap activation plan 也已改为严格 compact JSONL（一行一个 activation），避免 pretty
JSON 被逐行 consumer 误读为截断输入。当前完整回归为 680 项 JUnit 零失败；从 clean
work root 执行 `experiments/generic/three-thread-rpc/run.sh all` 会一直完成到
`target/three-thread-rpc/final/boolean_reach_condition.json`。

generic runner 现在还会把配置中的 `runtime_region_instances` 传给 scheduler；若 runtime
planner 已给 output capture 绑定 exact call/event occurrence，后续静态 refinement 会保留这份
更强的 identity。bootstrap projector 精确接受 importer 的旧、新两种 admission authority，
但所选 root 必须确实 symbolized，且不能属于 observation-only、concrete fallback、VM
placeholder 或 unforced environment requirement。2026-07-18 从空 work root 的 fresh run
在 82.97 秒内完成两次 producer path flip、自然异常 replay、final compose 和 Z3 proof。

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
用户报告。`run.sh all` 会继续执行无下游注入的自然回放，只有验证真实目标异常后才生成
`target/three-thread-rpc/final` 下的最终报告。

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
  -> SAT producer 输入绑定回真实定义；target 无注入执行并验证异常
Final composer + Z3 proof
  -> VALIDATED_FINAL SMT、关系证明、最终 reach condition
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

跨 RPC/codec/SASL 的值传播使用独立的 runtime-confirmed `EQUALITY` binding：它要求两端
canonical port、exact region instance、完整 value fingerprint 和 writer-before-reader 顺序，
但不要求序列化前后的对象 identity。它与共享 field 的 `READ_FROM` 保持不同 relation kind，
composer 按 edge、kind、instance 和 runtime witness 精确选择，二者不能互相替代。

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

领域 adapter 在 final relationship 中只能提供候选映射，不能把程序没有执行出来的
equality、cache、expiry、membership 或 codec 语义冒充 runtime fact。研究用 bootstrap
可以在 policy 明确授权后加入这些 contract，但必须逐项写入 approximation catalog，并保持
`complete=false`、`relationallyComplete=false`；HDFS-11741 checkpoint 使用的正是后一种
边界。

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
bootstrap composition、projection、natural replay、bounded campaign、final composition、
relationship proof 和 reach-condition extraction。成功时会生成
`final/boolean_reach_condition.json`。

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
| `ConcolicNaturalReplayValidator` | 检查最终自然传播、异常和无 branch override |
| `ConcolicStaticCatalogReuse` | 校验冻结 catalog/class-tree/schedule 哈希并加载一个 replay region |
| `ConcolicStaticCatalogManifest` | 发布可复用静态 catalog 的 immutable manifest |
| `run_engine.sh` | 配置驱动的通用阶段编排 |

custom JDK 位于 `third_party/OpenJDK-Concolic-Execution-Engine`。三线程端到端 fixture、拓扑、
配置和阶段脚本位于 `experiments/generic/three-thread-rpc`。

## 三线程最终自然回放验证

主流程通过以下闭环把 bootstrap 候选变成最终的自然传播证据：

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
5. 上述验证通过后，重新生成 `VALIDATED_FINAL` SMT、relationship proof 和最终
   `target/three-thread-rpc/final/boolean_reach_condition.json`。

这五步现已由 `experiments/generic/three-thread-rpc/run.sh all` 自动完成；最终 reach
condition 已由同一组 producer/target activation 的自然传播与异常证据验证。
