# GraphChecker：图引导的 region concolic execution、symbolic merging 与 SMT composition

> 交接状态：2026-07-17。本文按层级组织，新的 Codex 对话应从第 0、1 层开始，
> 再进入对应检查点。不要根据旧对话或旧产物推断完成状态。

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
|---|---|
| Hadoop 仓库 | `/Users/lizhenyu/Desktop/study/hadoop` |
| Hadoop commit | `ece33208b89a6a06c1b362d10fab31343fe5df13` |
| HDFS baseline 单测 | `org.apache.hadoop.hdfs.server.balancer.TestBalancerWithEncryptedTransfer#testEncryptedBalancer1` |
| fresh expiry controlled workload | `org.apache.hadoop.hdfs.server.balancer.CausynthControlledSecondKeyUpdateTestBalancerWithEncryptedTransfer#testEncryptedBalancer1`；本地派生 harness，只用于在同一 baseline 语义范围内稳定触发 second key update，不得称为上游原始单测 |
| 执行环境 | 本机、Docker 内的自定义 OpenJDK、`MiniDFSCluster` |
| 实验补丁 | `CAUSYNTH_FIXED_MINIDFSCLUSTER_LOOP_FREE_V1` |
| 补丁文件 SHA-256 | `352efc4dd9a3d4e0df4d0840754d63fce1a09509ad947f9c232e24f35372bb93` |
| 禁止事项 | 扩展到第三方系统、真实网络目标、攻击或利用工作流 |

任何后续检查点或新对话都必须继续注明上述仓库、commit、baseline 单测、受控派生
workload 和执行边界。这里的
“固定”是为了保证实验可复现和不越界，不是说分析框架只能用于 HDFS；核心
concolic/worklist/IR/composer 仍应保持项目无关。

## 第 1 层：新对话 30 秒交接

### 1.1 研究目标

系统要自动完成两种 capture goal，而不是定义多种领域 region 类型：

1. `TARGET_BRANCH`：只对最终会到达 fatal throw 的目标 branch 做一次定向 flip，
   得到到达异常的条件；不要求枚举目标 region 的所有路径。
2. `OUTPUT_CLOSURE`：对其他 region 记录真实 path conditions，逐个生成可行 flip，
   用 Z3 求新输入，进行无 branch override 的真实重跑，导入输入到输出关系，最后
   合并为 guarded relation。

所有节点都是 `REGION.*`。`producer`、`protocol`、`lifecycle` 只能作为普通英语描述
程序事实，不能作为 region 类型、capture mode 或可补充语义的 adapter 分类。

### 1.2 当前权威检查点

不同输出目录的 region 编号和 runtime instance 不可混用。当前权威状态是：

| 层次 | 权威产物 | 已完成 | 尚未完成 |
|---|---|---|---|
| 最终手写 one-DN N=4 关系 | `causynth-output/hdfs-11741-one-dn-runtime-bounded-n4-final-handwritten-v1/final_one_dn_runtime_bounded_n4.smt2` | 直接写出 `K_NN=K_BALANCER=K_CACHED_DEK=K_PARSED=K_DN`、四项 expiry transformer、四次 put、`REGION.15.out.122 -> REGION.0.in.117` 和 fatal 闭式；本机 Z3 实跑为 `sat,unsat,sat,unsat,unsat` | **这是用户明确要求的 hand-written/runtime-bounded diagnostic，不是 production composer output**；没有 automatic-composition manifest，也不能据此声称任意 N 或全图自动闭合 |
| fresh one-DN runtime-bounded N=4 | `causynth-output/hdfs-11741-one-dn-fresh-concolic-v10-act9-v1` 与 `causynth-output/hdfs-11741-one-dn-runtime-bounded-n4-fresh-z3-v1` | `ACT.UPSTREAM.9/REGION.15#call121202` seed、occurrence-4 expiry flip、无 override fresh replay、native `Iterator.remove` exact join、strict import 的 `MAP_REMOVE -> MAP_PUT x4` 连续 Map SSA、ordered-prefix/target/rebinding verifier 与旧五项 Z3 检查全部通过；raw materialization observation 还记录 `collectionSize=4` 和完整 key list | 只证明该 fresh path。旧 imported summary 有四个 entry-read witnesses但没有 production `finiteMapSnapshots` certificate；现 worktree helper 的一次 `/private/tmp` 审计重导能生成 certificate，但尚无仓库权威 re-import/composition artifact。未证明任意 Map 长度，也未覆盖 N=4 的全部 expiry branch 组合 |
| 通用核心 | 当前 worktree | scheduler、递归 graph/path worklist、Z3 input solver、真实执行 backend、strict importer、replay validator、runtime output-slice refinement、guarded merger、bounded composer、model projector、concrete natural-replay validator；最新全量 `mvn test` 为 563/563，finite-map/VM-placeholder partial scaffolds 的 importer/composer/runtime 三组 targeted tests 为 202/202 | 现有 tests 尚未覆盖两条 scaffold 的 fresh import/composition 端到端接线；controlled `ACT.30` 另暴露 `TARGET_BRANCH` static-input/materialization 剪枝缺口，见 9.1 |
| 当前值无关关系 | `causynth-output/hdfs-11741-diagnostic-bounded-unified-z3-v1` | one-producer 与 recursive two-producer bounded SMT 已生成；Z3 分别为 `sat,unsat,sat,sat` 与 `sat,unsat,unsat,unsat`；证明闭式等价、expiry family 非空、fatal 蕴含 `currentKeyId != stale K`；v10 另有 fresh exact `MAP_REMOVE` summary | 该目录自身仍是 source-bounded diagnostic，尚未与 same-instance controlled target bundle 由 production composer 重新闭合 |
| fresh v5i runtime | `causynth-output/hdfs-11741-pre-fix-ece33208-loop-free-v5i` | target 为 `ACT.49/REGION.0#call135176`；exact allKeys port 为 `REGION.0.in.97`，read-from 为 `REGION_EDGE.373`，writer 为 `REGION.27.out.34/#call100972` | writer 前态为空，只支持 initially-absent family；fatal replay 使用一次 lookup-result materialization，不是 upstream-only natural replay |
| v5k 静态与离线重聚合 | `causynth-output/hdfs-11741-pre-fix-ece33208-loop-free-v5k-reaggregate-v5i-call-edges-v4-linear` | `REGION.30.in.66` 精确映射 `DelegationKey.expiryDate`/`removeExpiredKeys#u11`；旧 v5i trace 重聚合保持 fail-closed | 不是 fresh v5k JVM execution；exact DN activation 仍 `symbolicReady=false`，且全局静态 coverage 因 50,000-edge cap incomplete |
| 保留的 v4 bounded replay | `causynth-output/hdfs-11741-pre-fix-ece33208-loop-free-v4` | `REGION.0` 无 override replay、`REGION.10` merge、bounded composition/model projection 和零下游注入 natural replay 均已验证 | 是有效历史局部证据，但不是当前 expiry-recursion 的 fresh runtime provenance；全局 graph worklist 仍有 62 gaps |
| 保留的 v3 回归证据 | `causynth-output/hdfs-11741-pre-fix-ece33208-loop-free-v3` | owner-aware field identity、mutable heap prestate、runtime slice refinement、target 与一个 `REGION.10` summary 均验证通过 | 只作历史比较；不得用 v3 dynamic IDs、summary 或 cache 替代 v4 证据 |
| 保留的 v2 回归证据 | `causynth-output/hdfs-11741-pre-fix-ece33208-loop-free-v2` | `REGION.0` 无 override replay/import 验证通过；真实 capture 暴露了 `REGION.10` admission 缺口 | `REGION.10` summary 不完整；该缺口已在 v3/v4 用通用 field identity、mutable heap prestate 和 runtime slice refinement 修复，不得复制 v2 dynamic IDs |
| 更早的 runtime 回归证据 | `causynth-output/hdfs-11741-pre-fix-ece33208-loop-free-v1` | `REGION.0` 无 override 定向 replay，`SUMMARY.REGION.0.dadadc35c016`，`targetReplayValidated=true`；campaign 真实执行过 1 个 `REGION.10` seed | campaign `complete=false`；只用于历史回归比较 |
| 更旧的历史证据 | `causynth-output/hdfs-11741-pre-fix-ece33208` | 保留用于回归比较的 `REGION.8`/`REGION.9` captures | 不得当作 `loop-free-v4` 的当前证据 |

保留的 `loop-free-v4` 静态产物指纹：

```text
symbolic_regions.jsonl:     d6b0c034fcd2b901519ce90401b0d3ca5e9ab4237b823c20934dc063fbc5742a
static_dataflow_edges.jsonl: 7df77fcbbd529192044cddef4b75ffeb8c2bfad5672a66c8a49eedb81aba4b08
```

生成 `v2` 前的 parser、constructor slice、input classification 和 instance-scoped target
query 修复继续保留。v3/v4 新增或强化的通用修复是：

- mutable `field_mutation` target 作为 canonical global heap prestate 输入，不能因同一
  region 的其他 constructor alternative 而被误判为已初始化；
- field identity 按 owner、type、name 精确匹配，同名 `allKeys` 字段不再跨 owner alias；
- output-slice input、heap initializer、causal edge 和 static site 按实际 runtime call tree
  精化；缺失 provenance 的旧产物保持保守并标记 refinement incomplete；
- output-slice binding 记录 `dependencyMethods` 和 causal-edge provenance；method-local cell
  可回退解析所属 method，包括 `<init>`；
- region entry/exit 使用 token 绑定生命周期；entry hook 到原始方法体的异常路径也进入
  cleanup trap，避免 nested/unselected root 错关 context；
- GraphChecker runtime bookkeeping 在 native PC 观察期间暂停；新 capture 带 isolation policy，
  strict importer 对 runtime-owned code position fail-closed；
- concrete replay 只把 Z3 model 投影到上游真实字段，下游 observation activation 禁止
  model、lookup materialization 和 forced branch；
- strict importer 的 input admission 未放宽，所有修复来自更准确的 static/runtime evidence。

自定义 OpenJDK 在一个 JVM、多线程和重复 region 下采用 TLS concolic context 加
process-wide non-blocking region owner lock：同一时刻只有一个 thread 可记录 symbolic PC，
竞争者 fail-closed；成功 owner 在 token 化的 exit/throw 中释放。显式 field/array
symbolization 可在 observation pause 内建立 symbolic state，但普通 Java bookkeeping 和
foreign-thread branch 不进入 PC。六组 native smoke 与 fresh HDFS PC audit 均已通过。

2026-07-16 历史全量回归检查点已通过：

```bash
mvn test
# Tests run: 485, Failures: 0, Errors: 0, Skipped: 0
```

HDFS 固定副本已应用显式的 loop-free 实验补丁，仅用于简化该固定
`MiniDFSCluster` 单测中的符号推导。`run_hdfs.sh` 在每个 HDFS 入口同时校验
commit、补丁 marker 和文件 SHA-256。不得将它误述为上游 Hadoop 原样语义。

通用核心已能持久化 summaries、path records 和 generated activations 并恢复 campaign。
当前可以声称明确标注 bounds 的 `REGION.10 -> REGION.0` 组合已由 Z3 求得模型并通过
无下游注入的自然传播 replay；不能把这个局部结论扩大为整个 HDFS upstream graph 已
自动闭合或某个全图 relationship 已完成蕴含证明。

### 1.3 新对话先校验

```bash
cd /Users/lizhenyu/IdeaProjects/GraphChecker
git status --short
git -C /Users/lizhenyu/Desktop/study/hadoop rev-parse HEAD
shasum -a 256 /Users/lizhenyu/Desktop/study/hadoop/hadoop-hdfs-project/hadoop-hdfs/src/main/java/org/apache/hadoop/hdfs/security/token/block/BlockTokenSecretManager.java
jq '{complete,methodPlanCount,staticEdgeCount,uncoveredMethodCount,uncoveredEdgeCount}' causynth-output/hdfs-11741-pre-fix-ece33208-loop-free-v4/symbolic_coverage.json
jq '{complete,methodPlanCount,staticEdgeCount,uncoveredMethodCount,uncoveredEdgeCount}' causynth-output/hdfs-11741-pre-fix-ece33208-loop-free-v5k-reaggregate-v5i-call-edges-v4-linear/symbolic_coverage.json
jq '{summaryId,finiteMapSnapshots,heapStateInitializers}' causynth-output/hdfs-11741-one-dn-fresh-concolic-v10-act9-v1/FLIP_U14_OCC4/concolic_region_summaries.jsonl
wc -l causynth-output/hdfs-11741-controlled-v5t-target-act30-production-v1/SEED/branch_queries.jsonl
bash -n experiments/hdfs/run_hdfs.sh
```

当前预期是旧 v10 imported summary 的 `finiteMapSnapshots` 不存在/为空、
`heapStateInitializers=[]`，controlled ACT.30 seed 的 `branch_queries.jsonl` 为 0 行；这些
是尚未闭合 production 自动化的事实，不应被当成校验失败后手工修产物。

Hadoop HEAD 必须精确等于：

```text
ece33208b89a6a06c1b362d10fab31343fe5df13
```

不要清理 dirty worktree，不要删除已有 capture，不要对 Hadoop 仓库执行 destructive
git 命令。`hs_err_pid*.log`、生成的 concolic classes 和用户已有改动都应保留，除非
用户明确授权清理。

### 1.4 精确续跑入口

用户列出的 v4 局部 TODO 已完成，不应无理由重复昂贵步骤：

```text
target instance:             REGION.0#call7000 / ACT.0
target map receiver:         REGION.0.in.25
target summary:              SUMMARY.REGION.0.c9acc805ae94
target replay:               validated, branchOverrideUsed=false
target exception chain:      SaslException -> InvalidEncryptionKeyException
captured upstream candidate: ACT.UPSTREAM.3 / REGION.10#call3565
upstream summary:            SUMMARY.REGION.10.e6b61e975747
upstream merged relation:    SUMMARY.REGION.10.MERGED.83e7f648d90b
input admission:             REGION.10.in.0 + REGION.10.in.6 complete
path worklist:               COMPLETE_BOUNDED_PATH_CLOSURE
relation merge:              COMPLETE_GUARDED_REGION_RELATIONS
bounded composition:         COMPLETE_BOUNDED_COMPOSITION
Z3 projection:               sat, projectionComplete=true
natural replay validator:    VALIDATED_NATURAL_UPSTREAM_PROPAGATION
downstream injection:        model=0, materialization=0, override=0
global graph worklist:       62 gaps, incomplete
```

有界 producer set 包含两个满足同一 test/region/root/requested-output、且位于目标前的
实例：`ACT.UPSTREAM.2/call3428/ordinal=1` 与已捕获的
`ACT.UPSTREAM.3/call3565/ordinal=2`。这是对一个 JVM 内两个 heartbeat threads 的保守
处理：全局 arrival ordinal 会随调度漂移，因此 model 被投影到这个精确声明的两个候选，
而不是假称仅凭 ordinal 就能稳定关联到单一动态 producer。两个上游 activation 各应用
6 个 model assignment；目标 activation 是 concrete observation-only，实际观察到 fatal
branch 和异常链，未注入 `HashMap.get=NULL`。

fresh PC isolation audit 使用最终 custom JDK 真实运行固定 HDFS 测试：7 个 inputs 均
symbolized、raw PC 有 21 条、目标 condition 唯一映射到 index 11，递归检查 runtime-owned
code position 数为 0。结束快照的 pause depth 2 来自 exit wrapper 与 `finish()` 正在抓取
summary，不是跨 region 泄漏；多轮 thread/GC/exception smoke 已验证 context 可恢复。

对 **v4 历史 scope**，下一个未完成步骤才是全局 graph closure 或进一步实现跨线程
producer 的稳定一对一 correlation。当前 v4 campaign 有 47 个 `UNPROVEN_REGION_EDGE`
gap 和 15 个 bound gap；不得用 HDFS 语义 adapter 填补。当前 one-DN 自动化的更近 TODO
是重导 v10 finite-map certificate、修复 controlled ACT.30 target-input pruning 并生成
validated target bundle、再跑 production composition；见 1.7 与 9.1。只有有意扩大 v4
已声明 bounds 时才恢复其 campaign；不得复制 v1/v2/v3 dynamic activation ID、
region/output cache 或 summary。

恢复前先读取当前 manifest，确认不是重复已完成 semantic query：

```bash
jq '{complete,eligibleToReportAutomaticRelationship,executionCount,solverQueryCount,
     graph: {complete: .graphWorklist.complete, gapCount: .graphWorklist.gapCount,
             status: .graphWorklist.status},
     paths: .pathWorklist.status, merge: .relationMerge.status, gaps}' \
  causynth-output/hdfs-11741-pre-fix-ece33208-loop-free-v4/unit-test-graphs/org.apache.hadoop.hdfs.server.balancer.TestBalancerWithEncryptedTransfer_testEncryptedBalancer1/concolic-schedule-REGION_0/campaign/concolic_campaign_manifest.json
```

局部结论的权威文件依次是：

```text
composed_fatal_region10_bounded_manifest.json
natural-propagation-region10-bounded-producer-set/model_projection_manifest.json
natural-propagation-region10-bounded-producer-set/natural_replay_validation.json
pc-isolation-audit-v1/concolic_region_results.jsonl
```

### 1.5 2026-07-16 值无关递归关系检查点

当前研究结论不是某个具体 Z3 model，而是所有 backward-live symbolized variables
满足的关系。令 stale lookup key 为 `K`：

```text
K = K_NN_A
  = K_BALANCER_CURRENT_AT_FILL
  = K_CACHED_DEK
  = parseInt(split(USERNAME, " ")[0])
  = K_DN_LOOKUP
```

前一轮 NN -> DN `addKeys()` 的 target-key quotient 为：

```text
previousSurvives = PREVIOUS_PRE_HAS_TARGET
                   && !(PREVIOUS_PRE_TARGET_EXPIRY < PREVIOUS_NOW)
previousMatch    = P0 == K || P1 == K || P2 == K || P3 == K
PRE_HAS_TARGET   = previousSurvives || previousMatch

TARGET_ENTRY_EXPIRY =
  ite(P3 == K, PE3,
    ite(P2 == K, PE2,
      ite(P1 == K, PE1,
        ite(P0 == K, PE0, PREVIOUS_PRE_TARGET_EXPIRY))))
```

其中最高匹配下标对应顺序执行的最后一次 `HashMap.put`。本轮 remove + four puts 与
目标 branch 的完整闭式是：

```text
fatal
<=>
B0 != K && B1 != K && B2 != K && B3 != K
&& (!PRE_HAS_TARGET || TARGET_ENTRY_EXPIRY < CURRENT_NOW)
```

expiry-move 子族进一步要求 `previousMatch && PRE_HAS_TARGET &&
TARGET_ENTRY_EXPIRY < CURRENT_NOW`。两轮 producer 和 target 必须选中同一 DN manager、
同一 `allKeys` 对象，并满足 previous -> current -> target happens-before 与无中间 mutation。
`CURRENT_KEY_ID` 属于当前 `B0..B3`，所以 fatal 蕴含 `CURRENT_KEY_ID != K`。

完整变量分区和任意轮递推见
`causynth-output/hdfs-11741-diagnostic-bounded-unified-z3-v1/recursive_symbolic_relation.md`。
DEK expiry、secret/encryption bytes、非目标 map entries 和本轮 incoming expiries 对立即
lookup 不 backward-live，组合时被存在量化消去；若再拼一轮 `addKeys`，最后匹配的本轮
incoming expiry 会重新成为下一轮活变量。

证据边界必须保持分离：

1. fresh v5i 的 exact DN writer 在 `removeExpiredKeys()` 前 map 为空，只支持
   `PRE_HAS_TARGET=false`；
2. v5i Balancer 的非空 map 属于不同 process/manager/map，不能替代目标 DN summary；
3. v5k 离线重聚合只证明 fail-closed：`ACT.UPSTREAM.2/REGION.30#call100972` 的
   `REGION.30.in.66` 仍 `observed=false`，activation 仍 `symbolicReady=false`；
4. 这是 2026-07-16 当时的历史 gap：它要求 fresh later non-empty `addKeys` 和真实
   expiry flip/replay/import；该 runtime provenance 已由 1.6 的 v10 occurrence-4 replay
   闭合，不再是当前 TODO。production target/composition 自动化的剩余边界见 1.7/9.1。

### 1.6 2026-07-17 fresh one-DN N=4 检查点

上面第 4 项所述 fresh expiry gap 已在新的、独立保留的 v10 scope 中闭合；旧 v5i/v5k
段落仍作为历史证据边界，不得用其 dynamic identity 替代 v10：

```text
source activation:       ACT.UPSTREAM.9 / REGION.15#call121202
replay activation:       ACT.PATH.d26d55b957be30a5
selected DN scope:       only the Balancer-interacting DN instance
map input/output:        REGION.15.in.32 -> REGION.15.out.122
target state edge:       REGION_EDGE.883 -> REGION.0.in.117
runtime map evidence:    AT_MATERIALIZATION size=4/full key list + four complete MAP_ENTRY_READ witnesses
scheduled flip:          removeExpiredKeys#u14 occurrence 4 -> false
model projection:        FLIP_CONDITION_DELTA_ONLY_V1, one assignment
branch override:         false
runtime remove join:     UNIQUE_HASHMAP_REMOVENODE_RECEIVER_RESULT_HASH_PLUS_RUNTIME_ENTRY_KEY_V1
importer remove join:    EXACT_INDEX_RECEIVER_VM_RESULT_INTEGER_HASH_AND_RUNTIME_ENTRY_KEY_V1
heap SSA:                MAP_REMOVE, MAP_PUT, MAP_PUT, MAP_PUT, MAP_PUT
state ordinals:          0->1->2->3->4->5
summary:                 SUMMARY.REGION.15.9386f88d34f1
replay verifier:         valid, failures=0, ordered prefix 6/6
Z3:                      sat, unsat, sat, unsat, unsat
```

权威文件：

```text
causynth-output/hdfs-11741-one-dn-fresh-concolic-v10-act9-v1/
  SEED/concolic_region_summaries.jsonl
  FLIP_U14_OCC4/concolic_region_results.jsonl
  FLIP_U14_OCC4/concolic_region_summaries.jsonl
  FLIP_U14_OCC4/path_replay_verification.v2.json

causynth-output/hdfs-11741-one-dn-runtime-bounded-n4-fresh-z3-v1/
  manifest.json
  runtime_bounded_n4_fresh_path.smt2
  runtime_bounded_n4_fresh_path.z3.txt
```

该检查点必须诚实称为 `fresh runtime-bounded N=4 captured path`。`N=4` 不能仅由四次
`Iterator.next()` 推出；它来自 raw `fieldObservations` 中同一 `REGION.15.in.32`、同一
map token 的 `collectionSize=4` 和未截断完整 key list，再与 mutation 前四个 complete
`MAP_ENTRY_READ` 做双射。本次四个 pre-map key 是 fresh execution 的 concrete immutable
entry witnesses：`1, 2, -1801356227, -1801356226`；四个 expiry 与四个后续 put key保持
symbolic。实际路径删除第 4 项，所以闭式为：

```text
fatal
<=>
K != P0 && K != P1 && K != P2
&& B0 != K && B1 != K && B2 != K && B3 != K
```

完整 N=4 guarded merge 模板仍是
`all(Bj!=K) && all(Pi!=K || Ei<NOW)`，但当前 fresh evidence 没有枚举全部 expiry
组合；不得把模板写成已由 fresh campaign 证明，更不得声称任意 N。

### 1.7 2026-07-17 最终手写 SMT 与 production 自动化边界

用户最终明确要求先交付手写版本，因此当前最终可直接喂给 Z3 的文件是：

```text
causynth-output/hdfs-11741-one-dn-runtime-bounded-n4-final-handwritten-v1/
  final_one_dn_runtime_bounded_n4.smt2
```

它**手工**把预期/既有 Java 字符串 round-trip 语义公理化为直接等式
`K_PARSED = K_CACHED_DEK`，没有手写 `javaParseInt` 函数；这不等于该 artifact 自动消费
了 controlled ACT.30 的 concat/split/parseInt AST。Map 也手工展开完整四项
`ite(Ei<NOW, remove, identity)` transformer；fresh occurrence-4 path 实际只捕获
`E0..E2>=NOW && E3<NOW`，所以完整四项模板是人工 bounded 泛化，不是 fresh guarded
merge。最终值无关关系是：

```text
K_NN = K_BALANCER = K_CACHED_DEK = K_PARSED = K_DN

fatal
<=>
all(Bj != K_DN)
&& all(Pi != K_DN || Ei < NOW)
```

本机 `z3` 实跑五项结果为：

```text
fatal                                        sat
fatal XOR closed_form                        unsat
fresh occurrence-4 expiry-move family        sat
fatal AND heartbeat reintroduces K            unsat
fatal AND target pre-entry survives           unsat
```

该 SMT 的 SHA-256 为
`5975a6579bf6a327fe7af78d6823fa47da8dcffda62ec477905053ad743645f6`；当前目录没有
production manifest，也没有单独保存 Z3 stdout，以上结果来自本机直接执行该文件。

这份文件是可检查的最终 bounded diagnostic，但**不是自动生成物**。截至交接时 production
自动化仍缺：同一 controlled workload 的 validated `ACT.30` target bundle、scheduler 的
target backward-live input pruning、用新 finite-map/VM-placeholder 逻辑重新 import fresh
REGION.15、production composer output/manifest，以及同一实例 NN/Balancer username producer
到 `REGION.0.in.51` 的 runtime edge。不得把手写文件或旧 workload 的 target summary混入
新 controlled instance 后称为自动 composition。
该手写模型也没有执行 model projection 或 natural replay；本轮结论仅是 bounded SMT
关系及其五项 SAT/UNSAT 检查。

## 第 2 层：统一设计

### 2.1 Region 只有 capture goal 差异

| Goal | 是否有 `targetBranch` | 所需闭环 |
|---|---:|---|
| `TARGET_BRANCH` | 是 | prefix + 最终 branch negation + model materialization + unforced replay |
| `OUTPUT_CLOSURE` | 默认无；flip replay 时仅作 validation target | seed capture + 全部 output-relevant flips + guarded merge |

旧值 `RELATIONAL_PRODUCER` 和 `RELATIONAL_PROTOCOL` 只在
`RegionCaptureGoal` 中作为输入兼容读取，任何新产物都不得写这些值。

### 2.2 自动闭环

```text
读取 fatal query
  -> 对 target region 只执行一次定向最终 branch flip
  -> 严格验证目标 branch、异常链、model materialization、无 override

while graph/path worklist 在 bounds 内仍有工作:
  若已有完整 OUTPUT_CLOSURE summary 存在 pending flip:
    取最新 output-relevant branch
    保留它之前的 path prefix
    negate 该 condition，丢弃旧 suffix
    Z3 求输入 model
    把 model 变成真实输入 materialization
    重跑固定单测，不允许 branch override
    验证 prefix 和目标 branch 是自然执行结果
    import 新 path summary
  否则:
    取一个由 runtime-validated edge 指向的 cache-miss region/output
    用同一 scheduler 构造 output slice 和 materialization plan
    重跑固定单测并 import seed summary
  更新 output-specific cache
  递归发现上游 region
  记录 cycles、bounds、unproven edges 和 admission gaps

当且仅当 path worklist 闭合:
  将同一 region 的 path summaries 合并为 guarded relation

当且仅当 graph/path/merge/target 全部闭合:
  送入统一 SMT composer
```

“flip”不是强制 JVM 走某条 branch。Z3 只能改变真实输入；replay validator 必须看到
未被 override 的 branch prefix 和目标 outcome。任何 forced branch 都只能用于旧的
instrumentation 诊断，不能进入自动推导证据。

### 2.3 稳定身份与恢复

- graph query key：`SHA-256_CANONICAL_SEMANTIC_QUERY_V1`；
- path flip key：`SHA-256_CANONICAL_FLIP_QUERY_V1`；
- dynamic activation/call IDs 不参与稳定 key；
- cache key 至少包含 `region + requested output`，不能只按 region 命中；
- campaign 持久化 `campaign_activations.jsonl`、`campaign_summaries.jsonl`、
  `region_path_records.jsonl` 和 merged summaries；
- resume 时也会读取每个已成功 import execution 的 `activation_plan.jsonl`。

## 第 3 层：证据权限与 adapter 禁区

### 3.1 什么可以进入自动 SMT

| 证据 | 可以做什么 | 不能做什么 |
|---|---|---|
| 静态 dataflow / port map | 发现 candidate region、端口和 capture slice | 直接断言跨 region equality、expiry、membership、codec 语义 |
| 完整 runtime value fingerprint | 对具体匹配 invocation 建立候选 equality | 把未匹配或不完整 fingerprint 当 equality |
| confirmed runtime write/read | 建立 versioned state read-from、order、identity | 用“先后出现”替代具体 write/read witness |
| 完整 concolic summary | 提供 path guard、输入到输出表达式、heap effects | 补写运行中没有观察到的领域结论 |
| guarded merge | 合并已验证的多条 path relation | 假定未探索路径不存在 |
| `EXPLICIT_CONTRACT` | 单独保存人工假设和缺失语义 | 进入 automatic composer 或被报告为 symbolic execution 结果 |

结构 fingerprint 是有界 canonical serialization 的 SHA-256 digest。自动 equality 要求
两端完整 fingerprint、具体 runtime binding 和相同 digest；其可信度依赖 SHA-256
collision resistance。任何 depth/node/reflection bound 都会把该证据降为不可组合 gap。

### 3.2 HDFS adapter 已被降权

`HdfsRegionPortMapper` 只能做名称到通用 region port 的格式/端口映射，并明确输出：

```json
{
  "mappingOnly": true,
  "semanticAssertionsAllowed": false,
  "eligibleAsRegionSummary": false,
  "eligibleForAutomaticSmt": false
}
```

它不得声明 codec round-trip、cache policy、expiry 或 map membership。人工提出但尚未由
真实 region summaries 推导的内容只能写入 `HdfsExplicitContracts` 生成的独立
`EXPLICIT_CONTRACT_REGISTRY`。composer 不接受该文件，并在 manifest 中写：

```text
domainSemanticAdapterUsed = false
explicitContractsIncluded = false
```

### 3.3 HDFS 数据流提示的地位

研究者给出的方向是：`keyId` 经过 NameNode → Balancer → DataNode，`allKeys` 经过
NameNode → DataNode，最终希望将 NameNode、Balancer、DataNode、allKeys、expiry 等
相关符号变量放入同一 SMT。

这些是分析方向和待验证的 port topology，不是可以硬编码的等式。每一段 equality、
read-from、时间条件和 membership 都必须来自真实 region concolic summary 或严格
runtime witness；缺失部分必须保留为 gap 或 `EXPLICIT_CONTRACT`。

## 第 4 层：完成状态与分层检查点

### P0：固定范围和可复现实验 — COMPLETE

Scope：固定 Hadoop 仓库、commit、HDFS-owned 单测和本机 `MiniDFSCluster`；禁止第三方
系统。

- `hdfs.properties` 固定仓库、commit、输出目录和 custom OpenJDK；
- `run_hdfs.sh` 在 build/process/test/schedule/campaign/map 等入口校验 HEAD；
- 顶层 README 和 HDFS 输出 manifest 重复记录研究边界。

### P1：静态 region 与运行时实例化 — STATIC/RUNTIME V4 COMPLETE FOR FIXED TEST

Scope：固定 Hadoop 仓库、commit、HDFS-owned 单测和本机 `MiniDFSCluster`；禁止第三方
系统。

- Soot 生成通用 `symbolic_regions.jsonl`、output slices 和 static graph；
- runtime trace 生成 activation、具体 branch occurrence、field/call evidence；
- static RPC/format mapping 默认不可组合；
- equality 只接受完整 runtime fingerprint；state edge 只接受 concrete read-from。

存在 mapping gaps 是有效结果，不应通过 adapter 填补。当前 v4 固定测试生成 2535 个
runtime region instances、2561 个 activations，其中 26 个 upstream activations、2206 个
replayable activations；edge validation 含 30 个 confirmed read-from、48 个 confirmed
runtime equality、22 个 unproven mapping、367 个 unconfirmed read-from 和 428 个
unobserved edges，trace 未截断。

### P2：fatal target 定向 concolic replay — COMPLETE ON V4

Scope：固定 Hadoop 仓库、commit、HDFS-owned 单测和本机 `MiniDFSCluster`；禁止第三方
系统。

真实证据：

```text
region:                 REGION.0
activation:             ACT.0
region instance:        REGION.0#call7000
target site:            BlockTokenSecretManager.retrieveDataEncryptionKey#u8
map receiver input:     REGION.0.in.25
occurrence:             1
observed -> desired:    true -> false
branch override:        false
test result:            1/1 passed
imported summary:       SUMMARY.REGION.0.c9acc805ae94
targetReplayValidated:  true
```

异常链包含外层 `SaslException` 和目标 `InvalidEncryptionKeyException`。这一步只证明
定向 fatal reachability 条件，不枚举 `REGION.0` 全部路径。v4 schedule、solver
materialization、真实 replay 和 strict import 均来自同一个 instance-scoped query；目标
branch 的实际结果为 false，未使用 override，test 仍为 1/1 passed，因为该异常是测试
预期路径的一部分。

### P3：通用 `OUTPUT_CLOSURE` summary — COMPLETE IN CORE

Scope：固定 Hadoop 仓库、commit、HDFS-owned 单测和本机 `MiniDFSCluster`；禁止第三方
系统。

- scheduler 根据 requested output 的静态 backward slice 构造 materializations；
- importer 要求所有 slice input 有真实 symbolization evidence；字段子路径可以覆盖其
  父输入端口；
- path condition、branch mapping、output expression 和 ordered heap effects 使用统一 IR；
- incomplete input/heap summary 不进入 path flipping。

以下是无 loop-free 后缀的历史回归产物，不是当前 `v4` 证据：

```text
summary:                 SUMMARY.REGION.8.af398b151a52
input admission:         complete
normalized path count:   23
branch mappings:         19
heap effects:            4
heap model:              complete
relationallyComplete:    true
branch override:         false
test result:             1/1 passed
```

真实 `REGION.9` seed 被严格保留为 incomplete：静态 slice 要求 14 个输入，运行中只观测
到 5 个 symbolized inputs，并有 null/field-resolution failures。它不能被翻转或作为完整
region relation 进入 composer。

v1/v2 campaign 暴露过 `REGION.10` input materialization/admission 不完整。v3/v4 没有
放宽 importer，而是把 mutable map prestate 明确建模为 `REGION.10.in.0`，并按 owner
区分 `BlockTokenSecretManager.allKeys` 与 `ExportedBlockKeys.allKeys`。最新真实证据为：

```text
source activation:             ACT.UPSTREAM.3 / REGION.10#call3565
summary:                       SUMMARY.REGION.10.e6b61e975747
merged summary:                SUMMARY.REGION.10.MERGED.83e7f648d90b
required/observed inputs:      REGION.10.in.0, REGION.10.in.6
input admission:               complete
ordered heap effects:          4 MAP_PUT
final heap output:             REGION.10.out.4
requestedOutputSliceComplete:  true
relationallyComplete:          true
branch override:               false
```

### P4：path flip、Z3 input 与 guarded merging — COMPLETE IN CORE, HDFS BOUNDED

Scope：固定 Hadoop 仓库、commit、HDFS-owned 单测和本机 `MiniDFSCluster`；禁止第三方
系统。

- `RegionPathWorklist` 采用 latest-decision-first；保留 prefix、negate target、删除 suffix；
- `ConcolicConstraintSolver` 生成可物化输入，而不是让用户查看具体 model 值；
- replay validator 拒绝 override、未应用 model、prefix 不匹配或 target 不匹配；
- `RegionSummaryMerger` 只在 worklist closed 时产生完整 guarded merge；
- 中立单元测试已覆盖 SAT/UNSAT、duplicate path、resume、alternative paths 和 incomplete
  summary rejection。

当前 v4 campaign 的已捕获 `REGION.10` 有 1 条 observed path、0 个 candidate flips、
0 个 path gap，状态为 `COMPLETE_BOUNDED_PATH_CLOSURE`；对应 guarded merge 也 complete。
这是声明 bounds 和已捕获 activation 内的局部 closure，不等于整个 HDFS graph closure。

### P5：递归 graph worklist、去重、bounds、cycle/gap — COMPLETE IN CORE

Scope：固定 Hadoop 仓库、commit、HDFS-owned 单测和本机 `MiniDFSCluster`；禁止第三方
系统。

- 按 region + output 递归发现上游 request；
- stable query key 排除动态 IDs；
- alternative writers 使用 guarded selection；
- unproven mapping 可用于发现，但 `captureRequired=false`、不可递归扩展、不可进入 SMT；
- max depth/regions/activations/alternatives/queries/paths/wall-clock 都有 manifest；
- cycle、bound、missing slice/activation、unproven edge 都是显式 gap。

### P6：自动 campaign 闭环与恢复 — COMPLETE IN CORE, HDFS IN PROGRESS

Scope：固定 Hadoop 仓库、commit、HDFS-owned 单测和本机 `MiniDFSCluster`；禁止第三方
系统。

`ConcolicCampaignRunner` 已自动完成：

```text
cache miss -> scheduler output plan -> Soot instrumentation -> fixed test
-> raw result -> strict import -> cache update -> path flips -> guarded merge
-> recursive re-plan
```

已有完整 summary 的 pending flips 优先于下一个 seed capture，避免先采集全部 region
才开始 symbolic merging。campaign 可跨多次 bounded 运行恢复 generated activations。

当前 v4 有界 campaign 实际执行 1 个 stable execution、导入 1 个 raw path summary、
生成 1 个完整 guarded relation。graph worklist 有 63 个 work items、141 个 upstream
requests 和 62 个显式 gaps，其中 47 个 `UNPROVEN_REGION_EDGE`、15 个
`BOUND_REACHED`；全局另有
`MAX_CAMPAIGN_EXECUTIONS` bound。因此 `complete=false`、
`eligibleToReportAutomaticRelationship=false`。

2026-07-17 的 controlled `ACT.30/REGION.0#call129678` production target capture 还暴露了
一个独立 scheduler gap：seed plan 把 REGION.0 的 broad static input set（128 个 symbols、
333 个 materializations）整体交给 Soot，而不是只保留目标 branch 的 backward-live inputs。
计划同时出现 `schedulerReady=true` 与 `materializationComplete=false`，随后
`process-concolic` 对 `REGION.0.in.53` 以
`ARRAY_VALUE_FIELD_REQUIRES_EXACT_LEAF_DECLARATION_AND_CONSUMED_SITE` fail-closed。
`branch_queries.jsonl` 因 capture-only seed 仍为空。修复必须发生在通用 scheduler 的
target-input pruning/readiness gate；不得手工删除 materialization plan 行绕过 admission。

### P7：统一 SMT composer 与 relationship proof — V4 BOUNDED COMPLETE, ONE-DN PRODUCTION/GLOBAL GRAPH BLOCKED

Scope：固定 Hadoop 仓库、commit、HDFS-owned 单测和本机 `MiniDFSCluster`；禁止第三方
系统。

- composer 只接受通用 fatal query、region summaries 和 runtime-validated bindings；
- target replay 必须有 `targetReplayValidated=true` 且无 override；
- missing/incomplete summaries、unsupported expressions 和 unbound ports 全部进 manifest；
- verifier 先检查 base SAT，再检查 `base AND NOT(relationship)` 是否 UNSAT；
- 若 candidate set 的 `eligibleForAutomaticVerification=false`，verifier fail-closed，完全
  不调用 Z3 proof，并将候选标为 `NOT_ELIGIBLE_INCOMPLETE_COMPOSITION`；
- `EXPLICIT_CONTRACT` 和 HDFS port map 永不参与自动 proof。

当前 v4 的明确有界 composition 只包含 `REGION.10` 与 `REGION.0`，状态为
`COMPLETE_BOUNDED_COMPOSITION`，runtime read-from 将 `REGION.10.out.4` 绑定到
`REGION.0.in.25`；base SMT 为 `sat`，并已把 model 投影到上游做自然 replay。这个 scope
允许报告 bounded composition/model/replay，不允许报告尚未执行的 negated-relationship
UNSAT proof。全局 graph worklist 仍未闭合，任何全图 composition/proof 必须继续报告
explicit gaps 并 fail-closed。

当前 worktree 有两条**部分落地、尚未端到端接通**的通用路径。VM placeholder 方面，
Importer 会生成 `vmIntrinsicPlaceholderBindings`，Composer 有 scope lookup scaffold，但
尚无把 summary catalog 注册/populate 到该 scope map 的代码，fresh `currentTimeMills#3`
仍会落入 unsupported fallback。finite Map 方面，Runtime 能记录
`FINITE_MAP_ENTRY_SNAPSHOT`，旧 raw field-observation 的 size/keys 与 entry reads 可由新
Importer helper 生成 `finiteMapSnapshots`，Composer也有 exact `MapState` encoder；但
`validateRuntimeHeapObservations` 仍只接受 `MAP_ENTRY_READ`，会拒绝新的 runtime snapshot
kind，且没有 fresh re-import/composition artifact。最新代码可编译，现有 importer/
composer/runtime 三组 targeted tests 为 202/202，全量 suite 为 563/563；这些 tests 尚未
覆盖上述 fresh artifact 完整接线。因此 P7 的生产结论不因本次手写 SMT 而升级。

## 第 5 层：关键代码

| 文件 | 职责 |
|---|---|
| `concolic/RegionCaptureGoal.java` | `TARGET_BRANCH` / `OUTPUT_CLOSURE` |
| `concolic/ConcolicScheduler.java` | target query、output materialization、instance-scoped merge context |
| `concolic/RecursiveRegionWorklist.java` | graph recursion、stable keys、cache、bounds/cycles/gaps |
| `concolic/RegionPathWorklist.java` | path flip worklist 与 stable path/flip keys |
| `concolic/ConcolicConstraintSolver.java` | Z3 query 与真实 input model assignments |
| `concolic/ConcolicCampaignRunner.java` | 自动执行/import/cache/replan 与 resume |
| `concolic/ConcolicReplayValidator.java` | 无 override 的 prefix/target validation |
| `concolic/ConcolicSummaryImporter.java` | strict summary admission 与统一 expression/heap IR |
| `concolic/RegionSummaryMerger.java` | guarded path relation |
| `concolic/AutomaticRegionEdge.java` | runtime equality/read-from evidence gate |
| `concolic/ConcolicSmtComposer.java` | 通用 SMT composition 与 explicit gaps |
| `concolic/ConcolicComposedModelProjector.java` | bounded Z3 model 到真实上游 activation 的投影 |
| `concolic/ConcolicNaturalReplayValidator.java` | 零下游注入的自然传播严格验证 |
| `concolic/SymbolicRelationshipVerifier.java` | base-SAT + negated-relation UNSAT proof |
| `causynth/HdfsRegionPortMapper.java` | HDFS 名称/端口映射；无语义 |
| `causynth/HdfsExplicitContracts.java` | 被排除的人工假设 registry |
| `runtime/ConcolicRegionRuntime.java` | 自定义 JDK runtime bridge |
| `experiments/hdfs/run_hdfs.sh` | 固定 HDFS workload 的 backend orchestration |
| `third_party/OpenJDK-Concolic-Execution-Engine` | TLS context、single-owner region、pause-aware explicit symbolization |

详细 IR 与组件不变量见 `docs/CONCOLIC_INTEGRATION.md`。

## 第 6 层：产物与读取顺序

```bash
TEST='org.apache.hadoop.hdfs.server.balancer.TestBalancerWithEncryptedTransfer#testEncryptedBalancer1'
TRACE='/Users/lizhenyu/IdeaProjects/GraphChecker/causynth-output/hdfs-11741-pre-fix-ece33208-loop-free-v4/unit-test-graphs/org.apache.hadoop.hdfs.server.balancer.TestBalancerWithEncryptedTransfer_testEncryptedBalancer1'
SCHED="$TRACE/concolic-schedule-REGION_0"
CAMPAIGN="$SCHED/campaign"
```

当前 `TRACE`、schedule 和 campaign 目录均已存在。先看 campaign manifest、target
summary、upstream merge 与明确有界的 composition/natural replay：

```bash
jq . "$CAMPAIGN/concolic_campaign_manifest.json"
jq 'select(.summaryId == "SUMMARY.REGION.0.c9acc805ae94")' \
  "$SCHED/concolic_region_summaries.jsonl"
jq . "$CAMPAIGN/merged_region_summaries.jsonl"
jq . "$SCHED/composed_fatal_region10_bounded_manifest.json"
jq . "$SCHED/natural-propagation-region10-bounded-producer-set/model_projection_manifest.json"
jq . "$SCHED/natural-propagation-region10-bounded-producer-set/natural_replay_validation.json"
```

主要文件：

| 文件 | 含义 |
|---|---|
| `$TRACE/concolic_activation_plan.jsonl` | runtime-discovered activations |
| `$TRACE/runtime_region_edge_validation.jsonl` | composable 与 mapping-only edge evidence |
| `$SCHED/branch_queries.jsonl` | fatal directed query |
| `$SCHED/symbolic_merge_plan.json` | target-instance-scoped equality/read-from plan |
| `$SCHED/concolic_region_summaries.jsonl` | validated fatal replay summary |
| `$CAMPAIGN/campaign_activations.jsonl` | 可恢复的 generated activations |
| `$CAMPAIGN/campaign_summaries.jsonl` | raw admitted region path summaries |
| `$CAMPAIGN/region_path_records.jsonl` | SAT/UNSAT/execution/replay terminal records |
| `$CAMPAIGN/merged_region_summaries.jsonl` | guarded merges，可能 incomplete |
| `$CAMPAIGN/concolic_campaign_manifest.json` | graph/path/merge/bounds/gaps 总状态 |
| `$SCHED/hdfs_region_port_map.json` | mapping-only，禁止进入 SMT |
| `$SCHED/hdfs_explicit_contracts.json` | 独立且被排除的人工假设 |
| `$SCHED/composed_fatal.smt2` | composed SMT，即使有 gap 也可生成供诊断 |
| `$SCHED/composed_fatal_manifest.json` | 是否允许报告自动关系的权威 gate |
| `$SCHED/symbolic_relationship_candidates.json` | 待证候选及 eligibility |
| `$SCHED/symbolic_relationship_proofs.json` | fail-closed proof report |
| `$SCHED/composed_fatal_region10_bounded.smt2` | 明确有界的 `REGION.10 -> REGION.0` SMT |
| `$SCHED/composed_fatal_region10_bounded_manifest.json` | bounded composition soundness scope |
| `$SCHED/natural-propagation-region10-bounded-producer-set/model_projection_manifest.json` | Z3 model 与两个 bounded producer 的投影证据 |
| `$SCHED/natural-propagation-region10-bounded-producer-set/natural_replay_validation.json` | 零下游注入的自然传播权威结论 |
| `$SCHED/pc-isolation-audit-v1/concolic_region_results.jsonl` | fresh custom-JDK raw PC isolation audit |
| `causynth-output/hdfs-11741-one-dn-fresh-concolic-v10-act9-v1/FLIP_U14_OCC4/concolic_region_results.jsonl` | fresh occurrence-4 raw runtime evidence；含 materialization size/keys、entry reads 与 remove/put trace |
| `causynth-output/hdfs-11741-one-dn-fresh-concolic-v10-act9-v1/FLIP_U14_OCC4/concolic_region_summaries.jsonl` | 旧 strict imported REGION.15 path summary；尚无新 finite-map/placeholder certificate 字段 |
| `causynth-output/hdfs-11741-controlled-v5t-target-act30-production-v1/SEED/` | 未完成的 ACT.30 production seed schedule；`branch_queries.jsonl` 为空，不是 validated bundle |
| `causynth-output/hdfs-11741-one-dn-runtime-bounded-n4-final-handwritten-v1/final_one_dn_runtime_bounded_n4.smt2` | 本轮最终手写 bounded diagnostic；无 production manifest/model projection/natural replay |

每次 execution 在：

```text
$CAMPAIGN/executions/<stable-prefix>/
  capture_request.json
  activation_plan.jsonl
  concolic_region_results.jsonl
  concolic_region_summaries.jsonl
  concolic_import_diagnostics.jsonl
```

## 第 7 层：命令

### 7.1 构建与全量回归

```bash
mvn -q test
mvn -q package -DskipTests
bash -n experiments/hdfs/run_hdfs.sh
```

最新改动后已执行：

```bash
mvn -DskipTests compile
mvn -Dtest=edu.uva.liftlab.graphchecker.concolic.ConcolicSummaryImporterTest,edu.uva.liftlab.graphchecker.concolic.ConcolicSmtComposerTest,edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntimeTest test
# Tests run: 202, Failures: 0, Errors: 0, Skipped: 0
mvn test
# Tests run: 563, Failures: 0, Errors: 0, Skipped: 0
```

全量 485/485 仍作为 2026-07-16 历史基线；当前权威回归结果是 563/563。

### 7.2 初次固定 HDFS 流程

```bash
TEST='org.apache.hadoop.hdfs.server.balancer.TestBalancerWithEncryptedTransfer#testEncryptedBalancer1'

experiments/hdfs/run_hdfs.sh build
experiments/hdfs/run_hdfs.sh compile
experiments/hdfs/run_hdfs.sh process
experiments/hdfs/run_hdfs.sh test "$TEST"
experiments/hdfs/run_hdfs.sh schedule-concolic "$TEST" REGION.0

TRACE='causynth-output/hdfs-11741-pre-fix-ece33208-loop-free-v4/unit-test-graphs/org.apache.hadoop.hdfs.server.balancer.TestBalancerWithEncryptedTransfer_testEncryptedBalancer1'
SCHED="$TRACE/concolic-schedule-REGION_0"
PLAN="$SCHED/scheduled_activation_plan.jsonl"
RESULTS="$SCHED/concolic_region_results.jsonl"
ACT=$(jq -r 'select(.captureGoal.kind == "TARGET_BRANCH") | .activationId' "$PLAN" | head -n 1)

test -n "$ACT"
experiments/hdfs/run_hdfs.sh process-concolic "$PLAN" "$ACT"
experiments/hdfs/run_hdfs.sh replay-concolic "$PLAN" "$ACT" "$TEST"
experiments/hdfs/run_hdfs.sh import-concolic "$PLAN" "$RESULTS"
```

`ACT` 必须从当前 `v4` scheduled plan 读取，不得从 v1/v2/v3 手工复制。导入后先
检查 summary 的 `targetReplayValidated=true`、`branchOverrideUsed=false` 和实际异常链，
再启动 campaign。Soot instrumentation 可能需要约三分钟；已有有效产物时不要无理由重跑。

### 7.3 有界 campaign 与恢复

```bash
CAUSYNTH_CAMPAIGN_MAX_ITERATIONS=8 \
CAUSYNTH_CAMPAIGN_MAX_EXECUTIONS=1 \
CAUSYNTH_CAMPAIGN_MAX_SOLVER_QUERIES=1 \
CAUSYNTH_CAMPAIGN_WALL_CLOCK_MS=1200000 \
CAUSYNTH_CAMPAIGN_EXECUTION_TIMEOUT_MS=1200000 \
experiments/hdfs/run_hdfs.sh campaign-concolic "$TEST"
```

有界运行因剩余 work/gap 返回 exit 2 是正常的；以 manifest 为准。以上参数精确重现
当前一次 execution 的检查点。恢复会复用 summaries、path records 和 activations，
不应重复已完成 semantic query；只有确有新 capture request 时才有意提高持久化
campaign 的 execution/solver bounds。

### 7.4 mapping、composition 与 proof

```bash
experiments/hdfs/run_hdfs.sh hdfs-port-map "$TEST"
experiments/hdfs/run_hdfs.sh compose-smt "$TEST"
```

本轮手写最终 bounded SMT 的独立检查命令是：

```bash
z3 causynth-output/hdfs-11741-one-dn-runtime-bounded-n4-final-handwritten-v1/final_one_dn_runtime_bounded_n4.smt2
# sat, unsat, sat, unsat, unsat
```

该命令不产生/验证 production composition manifest。

若 composition incomplete，verifier 应返回 exit 2，并输出
`RELATIONSHIP_PROOF_BLOCKED_BY_COMPOSITION_GAPS`。这不是 Z3 失败，而是 soundness gate
正常工作。

已存在 bounded SMT 时，model projection 与完整自然 replay 的入口为：

```bash
experiments/hdfs/run_hdfs.sh project-composed-model "$TEST"
experiments/hdfs/run_hdfs.sh run-natural-replay "$TEST"
experiments/hdfs/run_hdfs.sh validate-natural-replay "$TEST"
```

当前三步均已有有效 v4 产物，不应无理由重跑。`run-natural-replay` 允许 HDFS-owned
test 在目标异常形成后非零退出，但最后必须由 strict validator 校验两个 bounded
producer、目标 branch/exception chain 和零 downstream shortcut；不能按进程 exit code
单独接受结果。

## 第 8 层：何时才能说“自动推导并由 Z3 验证”

必须同时满足：

```text
target summary:
  valid
  targetReplayValidated
  branchOverrideUsed == false
  expected model/materialization applied
  desired fatal branch and exception observed

upstream campaign:
  graphWorklist.complete
  pathWorklist.complete
  relationMerge.complete
  no unproven edge / cycle / bound / admission gap

composition:
  all relevant summaries complete
  no unsupported expression
  no unbound port
  runtime-selected equality/read-from witnesses only
  domainSemanticAdapterUsed == false
  explicitContractsIncluded == false
  eligibleToReportAutomaticRelationship == true

proof:
  eligibleForAutomaticVerification == true
  base SMT == sat
  base AND NOT(relationship) == unsat
```

Z3 输出某个具体 model 不是研究结论。研究结论是：concolic execution 选择了哪些
branch、每条 path 的 symbolic guard 是什么、region 输入输出如何合并，以及 composed
constraints 是否逻辑蕴含某个 symbolic relationship。

当前必须区分六类 soundness scope：

- fresh one-DN runtime-bounded N=4 path：v10 `ACT.UPSTREAM.9` seed 与
  `ACT.PATH.d26d55b957be30a5` occurrence-4 replay 已由 customized JDK 真正捕获
  `MAP_REMOVE`，strict importer 得到连续 `REMOVE -> PUT x4` Map SSA，独立 verifier
  对 ordered prefix、scheduled target、fresh entry rebinding 和 output closure 全部通过。
  raw materialization observation记录 size=4/full key list，另有四个 complete entry reads；
  旧 imported summary 尚未把二者认证为 `finiteMapSnapshots` initializer。旧 Z3 文件对
  手工绑定的 four-entry witness/captured path 得到 `sat,unsat,sat,unsat,unsat`。这是
  fresh path provenance 加 bounded assembly，不是 production composer 已自动证明 exact
  finite domain。
- 最终手写 one-DN N=4 diagnostic：
  `final_one_dn_runtime_bounded_n4.smt2` 按用户要求给出完整四项 expiry transformer 和
  key-chain 公理，Z3 为 `sat,unsat,sat,unsat,unsat`。其 closed-form equivalence 只证明
  手工公式的内部 Array/store 语义；不证明完整 N=4 guarded merge、字符串链或 NN edge
  已由当前 controlled runtime 自动捕获/组合。
- relation-level bounded diagnostic：`full_symbolic_relation.smt2` 与
  `recursive_symbolic_relation.smt2` 不固定具体 key/time；SAT 证明 family 非空，
  `base AND NOT(closed-form)` 为 UNSAT 证明值无关闭式等价。这是关系级证明，不自动
  提升为 fresh runtime provenance。
- fresh v5i runtime：精确 target/writer/read-from 已确定，但 selected DN writer 的
  pre-map 为空，且 fatal replay 使用一次 lookup materialization；只能支持
  initially-absent family，不能报告 expiry-remove natural propagation。
- v5k offline reaggregation：新静态目录正确找到 `REGION.30.in.66` expiry port，但旧
  native trace 没有对应 getter/field probe，所以 exact DN activation 保持
  `symbolicReady=false`。这是 soundness/fail-closed 诊断，不是 fresh capture。
- 保留的 v4 bounded natural replay：target replay、`REGION.10` path/merge、runtime
  read-from 与上游 model projection 均已严格验证，仍是有效的不同有界 scope。

其中保留的 v4 scope 还要区分：

- 明确有界的 `REGION.10 -> REGION.0` scope：target replay、`REGION.10` path/merge、
  runtime-confirmed read-from、owner-exact `REGION.0.in.25` binding 均已通过；composition
  manifest 为 `COMPLETE_BOUNDED_COMPOSITION`，无 missing summary、unsupported expression
  或 unbound port，且 Z3 base query 为 `sat`。model 已投影到精确声明的两个 pre-target
  producer 候选，随后 concrete replay 在下游零 model、零 lookup materialization、零
  override 时自然观察到 fatal branch 与异常链。因此可以报告“局部有界 composition
  求模并自然传播验证完成”。
- 全局 HDFS graph scope：graph worklist 仍有 62 gaps，campaign 因
  `MAX_CAMPAIGN_EXECUTIONS` 为 incomplete，故全局
  `eligibleToReportAutomaticRelationship=false`。此外当前有界 candidate 虽标记
  `eligibleForAutomaticVerification=true`，尚未生成 negated-relationship proof report，
  所以不能报告 `base AND NOT(relationship) == unsat` 的逻辑蕴含结论。

自然 replay 是 model 可物化与程序传播证据；它不替代全图 closure，也不替代尚未执行的
relationship entailment proof。

对 v10 N=4 scope，`runtime_bounded_n4_fresh_path.smt2` 的第二项 UNSAT 已完成其手工绑定
Array/store 模型与 captured-path 闭式的 entailment proof；最终手写文件的第二项 UNSAT
则证明完整四项 bounded transformer 与通用 N=4 闭式等价。两者都不提升全局 graph
scope，也不替代 production finite-domain certificate、ACT.30 target bundle 或任意 N 证明。

## 第 9 层：当前已知 gaps 与下一步

### 9.1 2026-07-17 当前状态

v10 已闭合旧清单中的首要 **runtime** gap：同一 selected DN 的 later non-empty
`addKeys()` 已被 fresh customized-JDK replay，occurrence-4 expiry flip 自然执行
`Iterator.remove()`，没有 branch override 或下游 lookup/result 注入。Runtime 只在 exact
`ENTRY_SET`、唯一 5 参数 `HashMap.removeNode`、receiver/result/Integer hash-spread 和
activation-local entry tokens 全部一致时 rebind opaque boxed key；Importer 会独立重证。

本轮最终交付也已完成：按用户明确要求生成手写 runtime-bounded N=4 SMT，本机 Z3 为
`sat,unsat,sat,unsat,unsat`。因此“给出一份可求解并表达 expiry-move 解族的最终 bounded
SMT”这一任务完成。下面条目是若以后继续追求 **production 全自动版本** 时必须保留的
TODO/GAP，不是对本轮手写交付的阻塞。

已完成的证据：

1. `FLIP_CONDITION_DELTA_ONLY_V1` 只物化目标 guard 的 expiry symbol，不把无法控制的
   `currentTimeMillis` model 值强塞给 prefix。
2. fresh replay 1/1 通过，实际 heap SSA 为 `MAP_REMOVE -> MAP_PUT x4`，状态连续 `0->5`；
   ordered-prefix、scheduled-target、entry rebinding 和 output-closure verifier 均通过。
3. raw materialization observation 给出同一 map token 的 `collectionSize=4` 和完整 keys，
   mutation 前另有四个 complete `MAP_ENTRY_READ`；exact state edge 为
   `REGION_EDGE.883: REGION.15.out.122 -> REGION.0.in.117`，producer/target receiver 与
   value object identity 一致。
4. 最终手写文件把完整 N=4 expiry transformer 与 closed form 放在同一 SMT 中；Z3 已证明
   family 非空、closed form 等价、reintroduction/surviving-target 与 fatal 互斥。
5. 当前源码可编译；现有 `ConcolicRegionRuntimeTest`、`ConcolicSummaryImporterTest`、
   `ConcolicSmtComposerTest` 合计 202/202 通过。

当前 production 自动化 gaps：

1. **最终文件是手写 diagnostic。** `K_PARSED=K_CACHED_DEK` 是人工 Java-library
   round-trip 公理，完整四项 `ite(Ei<NOW,remove,identity)` 是从单一路径人工泛化；它们
   不是本次 controlled target bundle 自动 lowering/guarded merging 的输出。文件没有
   automatic-composition manifest。
2. **controlled ACT.30 target bundle 未生成。** 当前仅有
   `hdfs-11741-controlled-v5t-target-act30-production-v1/SEED`。它精确选择
   `ACT.30/REGION.0#call129678`，但 `boundaryReady=false`、
   `staticInputSelectionComplete=false`、`materializationComplete=false`；
   计划含 128 个 symbolize rows、333 个 materializations 和 20 个 static unresolved inputs；
   `branch_queries.jsonl` 为 0 行，也没有 target replay/import/validated summary。
3. **TARGET_BRANCH input pruning/readiness 有 bug。** Scheduler 把 REGION.0 的 broad
   static inputs/333 materializations整体交给 Soot，并同时写出 `schedulerReady=true`。
   `process-concolic` 随后在 broad alias projection `REGION.0.in.53` 上以
   `ARRAY_VALUE_FIELD_REQUIRES_EXACT_LEAF_DECLARATION_AND_CONSUMED_SITE` fail-closed。
   必须在通用 backward-live selection/readiness gate 修复；不得手删 plan 行。
4. **finite Map certificate 尚未接通 production。** 旧 v10 imported summary 没有
   `finiteMapSnapshots` 且 `heapStateInitializers=[]`；四个 reads 单独只能证明至少四项。
   当前 Importer 已能从旧 raw 的 materialization size/full keys + four reads 生成 N=4
   certificate；一次只写到 `/private/tmp` 的审计重导得到
   `SUMMARY.REGION.15.bdbfe07ed2a7`、`relationallyComplete=true`，但它不是仓库权威产物且
   尚未 compose。Worktree Runtime 另新增 `FINITE_MAP_ENTRY_SNAPSHOT`，然而
   `validateRuntimeHeapObservations` 仍只接受 `MAP_ENTRY_READ`，新 kind 会被拒绝；Runtime
   支持的 cardinality/key schema 与旧-certificate helper 的 `<=32`、整数 wrapper范围也
   尚未统一。
5. **NOW binding 仍是 partial scaffold。** Importer 能生成受证
   `vmIntrinsicPlaceholderBindings`，Composer 有 lookup，但没有把 catalog 注册到当前
   summary/case scope；因此 fresh `currentTimeMills#3` 仍可能成为 unsupported placeholder。
   不得把不同动态 clock identity（例如 `#1` 与 `#3`）错误合并。
   `RegionSummaryMerger` 也尚未把 finite-map/placeholder certificate 与 admission 字段复制
   到 guarded cases，merge 后会丢证据。
6. **same-instance key-chain 证据不完整。** Map read-from edge 883 已精确；但当前 runtime
   ledger 没有同一 instance 的 producer edge把 NN/Balancer cached key 接到 username input
   `REGION.0.in.51`。Production composer 的严格
   `parseInt(split(concat(toString(K),...)," ",0)) -> K` lowering 代码存在且 synthetic
   regression 已通过，但缺 controlled
   ACT.30 captured AST/target summary和 upstream runtime edge，故整条
   `K_NN=K_BALANCER=K_DN` 仍不能标为本次自动推出。ACT.30 merge plan 对
   `REGION.0.in.117` 还保留 `REGION_EDGE.857/883/675` 的
   `EXACTLY_ONE_GUARDED` alternatives；手写 one-DN 文件按声明 scope 固定选择 edge 883，
   不是 production composer 已自动合并/消歧全部 writers。
7. **path/cardinality bounds。** Fresh 只覆盖 seed no-remove 与 occurrence-4 removal；完整
   N=4 guarded merge还需其余 output-relevant guards或受证 loop summary。任意 N 未证明；
   不同 runtime cardinality 必须保持为不同 bounded cases。
8. **更大 scope 仍未闭合。** v4 全局 graph 仍有 62 gaps；跨 heartbeat thread 的稳定
   一对一 producer correlation 未实现。这不影响手写 one-DN bounded 结论。
9. **回归边界。** 最新 compile、202 项 targeted tests 与全量 563/563 均通过；仍没有
   fresh import/composer/Z3 artifact integration test，因此单元回归通过不能替代
   production evidence。

DPOR/系统化 thread-interleaving enumeration 是用户明确排除的当前范围，不列为 TODO；
当前只要求单线程 region summary 在跨 region composition 时保持 execution/instance/path
scope 隔离。

若以后继续自动版本，严格顺序是：

```text
1. 修复 TARGET_BRANCH backward-live input pruning 与 scheduler readiness gate；
2. 重建 controlled ACT.30 query，做无 override target replay/import，得到 validated bundle；
3. 接通 FINITE_MAP_ENTRY_SNAPSHOT runtime -> importer -> composer，并完成 NOW scope registration；
4. 用新 importer 重导 v10 raw，生成新 summary/cache identity；
5. 捕获/验证同实例 username key producer edge与字符串 AST；
6. production compose REGION.15 -> REGION.0，要求 manifest 无 unsupported/unbound/adapter/contract；
7. 跑 Z3 base 与 negated closed-form proof；需要完整 N=4 merge时再有界探索其余 guards；
8. 跑 targeted integration tests 与全量 mvn test。
```

### 9.2 2026-07-16 历史清单（已被 9.1 部分取代，不得作为当前 TODO）

1. 当前 expiry-recursion 的首要 gap 是同一目标 DN、同一 manager/map 的 exact
   `MAP_REMOVE` 尚未被 fresh customized-JDK capture；源码 guard/effect transformer 只能
   保持 `diagnostic/source-bounded`。
2. fresh v5i selected DN writer 在 `removeExpiredKeys()` 前 map 为空，只支持
   `PRE_HAS_TARGET=false`；重复该 first-registration activation 仍不能证明 expiry family。
3. v5k static `REGION.30.out.43` 的 requested output slice/capture/refinement 均 incomplete；
   `REGION.30.in.66` 虽由唯一 accessor callsite 精确发现，但旧 trace 中 `observed=false`。
4. v5k 离线重聚合不是 fresh v5k JVM execution，明确
   `eligibleAsNaturalReplayEvidence=false`；不得把新静态 catalog 与旧 probe trace 拼成
   自动 summary。
5. v5k 静态图达到 50,000 edge cap：1397 method plans、1120 uncovered methods、37722
   uncovered edges，global coverage incomplete。
6. 保留的 v4 graph worklist 有 62 个显式 gaps：47 个 `UNPROVEN_REGION_EDGE`，15 个
   `BOUND_REACHED`；不能用 HDFS 名称或协议知识补成 equality/read-from。
7. v4 campaign 已达到声明的 `MAX_CAMPAIGN_EXECUTIONS=1`，所以全局 manifest 明确为
   `complete=false`、`eligibleToReportAutomaticRelationship=false`。
8. v4 局部 bounded scope 已不再是 gap：`ACT.UPSTREAM.3/call3565` capture、guarded merge、
   `REGION.10 -> REGION.0.in.25` SMT composition、Z3 model projection 和无下游注入的
   natural replay 均完成。
9. producer activation 的全局 arrival ordinal 会在两个 heartbeat threads 间漂移。
   当前 replay 通过精确声明的两个 pre-target equivalent producers 做 bounded broadcast；
   这解决本次有界验证，但不是稳定的一对一动态 call correlation。
10. v4 natural replay 为两个 producer 都应用模型后，两台 DataNode 都经历目标异常；严格
   validator 已在目标 branch/exception 证据形成后通过，但 Maven/Surefire 顶层进程随后因
   两个节点均被排除而非零退出。不得把该非零退出误写成 validator 失败，也不得把它写成
   固定 HDFS 单测整体成功。
11. fresh HDFS symbolic audit 的 raw PC=21、symbolized inputs=7、runtime-owned PC
   positions=0；target branch candidate count=1。custom JDK 的 TLS/owner-lock、重复 region、
   foreign-thread isolation、GC 和 exception cleanup 另有六组 smoke 覆盖。
12. v1/v2 的 `REGION.10` input admission gap 已在 v3/v4 消除：最新 summary 严格观测
   `REGION.10.in.0` 与 `REGION.10.in.6`，不能再把旧 gap 当作当前阻塞点。
13. 2026-07-16 当时 worktree 的全量 `mvn test` 已执行，485/485 通过；这不是 2026-07-17
    partial scaffold 修改后的全量回归。
14. 固定 HDFS 副本已应用 `CAUSYNTH_FIXED_MINIDFSCLUSTER_LOOP_FREE_V1`
   实验补丁；其语义边界和 SHA-256 必须随每个检查点保留。

历史优先顺序（其中 fresh capture/flip/import 已由 v10 完成，不得重复）：

```text
1. 使用 v5k instrumentation 启动真正 fresh 的固定 HDFS workload；
2. 捕获同一目标 DN、同一 manager/map 的 later non-empty `addKeys` activation；
3. 对 expiry guard 做真实 concolic flip、无 branch override 重跑和 strict import；
4. 用 customized-JDK summary 替换当前源码 `MAP_REMOVE` transformer；
5. 重新组合 recursive bounded SMT，并保留值无关 closed-form proof；
6. 只把 model 投影到上游，目标禁止 lookup materialization、lookup result 注入和 override；
7. 做完整 natural replay validation；
8. 不要重复已经完成的 v4 target replay/natural replay，也不要用 HDFS adapter 或离线
   reaggregation 填 runtime provenance gap；
9. 每次修改后运行相关回归和全量 `mvn test`，并按新 manifest 更新检查点。
```

## 第 10 层：给新 Codex 的可复制提示

```text
请先完整阅读 readme.md 第 0、1、8、9、10 层，再继续当前检查点。

这是纯学术软件工程/程序分析项目。范围固定为：
- Hadoop repo: /Users/lizhenyu/Desktop/study/hadoop
- commit: ece33208b89a6a06c1b362d10fab31343fe5df13
- upstream baseline test:
  org.apache.hadoop.hdfs.server.balancer.TestBalancerWithEncryptedTransfer#testEncryptedBalancer1
- controlled expiry diagnostic workload:
  org.apache.hadoop.hdfs.server.balancer.CausynthControlledSecondKeyUpdateTestBalancerWithEncryptedTransfer#testEncryptedBalancer1
  （本地派生 harness，不是 upstream 原样单测）
- local MiniDFSCluster/custom OpenJDK only
- experimental patch: CAUSYNTH_FIXED_MINIDFSCLUSTER_LOOP_FREE_V1
- pinned patch SHA-256: 352efc4dd9a3d4e0df4d0840754d63fce1a09509ad947f9c232e24f35372bb93
- 禁止扩展到第三方系统或攻击/利用场景

统一设计仍是：fatal region 只做最终 directed branch；其他 region 做 OUTPUT_CLOSURE，
通过真实 record/flip/replay/import 得到 guarded relation，再交 production composer。
HDFS adapter 不得补 expiry、membership、codec 或 cache 语义；DPOR/thread-interleaving
enumeration 不在当前 TODO。

当前交付已完成，没有活动实验：
- fresh upstream evidence:
  causynth-output/hdfs-11741-one-dn-fresh-concolic-v10-act9-v1
  ACT.UPSTREAM.9 / REGION.15#call121202，occurrence-4 replay真实捕获
  MAP_REMOVE -> MAP_PUT x4；selected one-DN map edge 是
  REGION_EDGE.883: REGION.15.out.122 -> REGION.0.in.117。
- final hand-written bounded SMT:
  causynth-output/hdfs-11741-one-dn-runtime-bounded-n4-final-handwritten-v1/
  final_one_dn_runtime_bounded_n4.smt2
  Z3 = sat,unsat,sat,unsat,unsat。

必须明确：最终文件是按用户要求手写的 runtime-bounded N=4 diagnostic，不是 production
composer/campaign output。`K_PARSED=K_CACHED_DEK` 和完整四-entry expiry transformer是
手工公理/泛化；fresh path只捕获前三项 survive、第四项 remove。该文件没有 manifest、
model projection 或 natural replay，也不证明任意 N、完整 N=4 guarded merge或全图 closure。

只有用户以后再次要求 production 全自动版本时，才按 9.1 顺序继续。当前关键 gaps 是：
- controlled ACT.30 target bundle只有 SEED schedule；branch query=0，target replay/import缺失；
- scheduler未按 target backward-live slice剪掉 broad unsupported materializations；
- old v10 summary没有 finiteMapSnapshots；新 runtime snapshot kind尚未被 importer接受；
- RegionSummaryMerger会丢 finite-map/placeholder certificates；
- Composer placeholder scope catalog未注册，NOW仍会 unsupported；
- edge883只闭合 Map，username REGION.0.in.51缺 same-instance upstream key producer edge；
- production compose/manifest/relationship proof尚未执行；全量563/563已通过，v4全图仍62 gaps。

历史 v5i/v5k/v4 scope继续保留，但不是当前下一步。先检查 git status，不要清理现有改动，
不要复制旧 dynamic IDs，不要混用不同 workload/instance/process 的 summaries，也不要把
手写公理、临时 /private/tmp 重导或离线重聚合写成 production runtime evidence。
```
