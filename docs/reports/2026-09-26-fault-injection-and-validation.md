# 故障注入与验证：实现、图的变化、新 bug 与假阳性过滤（2026-09-26）

本报告对应目标："完善 fault injection 与 replay；在 HDFS 中寻找更多 ad-hoc
协调检查并尝试用 GraphChecker 找新 bug；总结注入故障后因果图的变化并配示意图与具体
case；给出 validation 真正过滤假阳性的例子并解释；修 GraphChecker 的 bug。"

所有数字都来自本仓库的运行产物（`~/gc-out/accept-<round>-<case>`），提交号都在
`main`（本地，未推送）。

---

## 0. 结论摘要

| 项 | 结果 |
|---|---|
| 故障注入 | 门由声明织入（`DOOR` 行 + `DoorWeave`），不再手写；每个门按"调用方区分的环境异常"给出多种故障：IPC 请求门 `IOException`/`ConnectTimeoutException`，IPC 响应门 `IOException`/`EOFException`/`SocketTimeoutException`，SASL 门 `IOException`。语义异常从不注入。 |
| 重放 | 探索阶段保持全序；**只有 SAT 之后的 CONFIRM 用偏序**：录制顺序不再保持（只有 WAKE 仍"不早于录制"），改为保持模型的读写来源顺序（写者 activation 退出后读者 activation 才进入，竞争写者排在外面）；等不到就是 `CONFIRM_MISMATCH`——卡死即假阳性。 |
| 九个 case | **v54 9/9 PASS**，全部过因果锥；`.smt` 保持路径选择器的 ite 组合 + `fatal_target` 查询，11741 由偏序 CONFIRM 重放确认（§5）。 |
| 新 bug | **找到一个真 bug 并在 trunk 复现**：外部 SPS / Balancer 的 id 文件"自持租约"——`create` 的响应丢失后，重试把自己的租约误判为"另一个实例在运行"，SPS `terminate(-1)`，Balancer 服务停摆到租约硬上限。它是静态调研 + 定向复现找到的；GraphChecker 当前的模型表达不了它（§3.3 解释为什么）。另用 GraphChecker 试了 key 家族的一个新检查点（block token 缺 key，§3.4）：146 次重放、所有门故障都没让它出错，结论是有依据的"不存在"——NameNode 预发下一个 key 保护了 token 路径。 |
| 图的变化 | 69 个故障重放（v51）+ 114 个（v53）逐一对照种子，扣除对照组噪声后归成 9 种模式；§4 用方块-线条图配具体 case。 |
| 假阳性过滤 | §6：E1（去掉跨线映射 → 公式在录制取值下就可满足、与健康录制矛盾 → COMPOSE 拒绝）；探索阶段 6 个被执行否决的 flip；E2（受控：模型要求的读写来源在这个世界里不存在 → 偏序门 60 s 等不到 → CONFIRM 拒绝；对照组确认）。 |
| 修掉的 GraphChecker bug | 反射访问站点随 JVM 预热漂移；lineage-only daemon 线程无节点归属（BPServiceActor 心跳落到 `unregistered`）；门织入后声明的循环 id 失配；偏序 CONFIRM 在同一 occurrence 内建门导致 11741 漏报（§7）。 |

---

## 1. 故障注入的完善

### 1.1 之前的样子

故障点是手写在每棵 Hadoop 树里的三处 `Debug.makeSymbolicBoolean("FAULT:…")`（9 棵树 × 3 处），每处只有一种故障（笼统的 `IOException`）。

### 1.2 现在的设计（`3cc1b7d29`）

```
communication-mappings.jsonl                    causynth（每一遍分析之前）
┌───────────────────────────────────────┐       ┌────────────────────────────────────┐
│ {"kind":"DOOR",                       │       │ DoorWeave.apply()                  │
│  "transport":"HADOOP_IPC",            │──────►│  在 method 里 after/before 的调用处 │
│  "direction":"RESPONSE",              │       │  按 faults 顺序织入：               │
│  "method":"<Client: getRpcResponse>", │       │   if (Debug.makeSymbolicBoolean(   │
│  "after":"<CompletableFuture: get()>",│       │        "FAULT:HADOOP_IPC:RESPONSE  │
│  "faults":["java.io.IOException",     │       │         [:EOFException]"))         │
│            "java.io.EOFException",    │       │      throw new EOFException(..);   │
│            "java.net.SocketTimeout…"]}│       └────────────────────────────────────┘
└───────────────────────────────────────┘                    │ 分析把 marker 当根（已有机制）
                                                             ▼
                                               规划 / 探索 / compose / CONFIRM 不变
```

* **在分析之前织入**：`CausynthPipeline.run()` 第一行调用 `DoorWeave.apply()`，
  所以讨论、录制、concolic 三遍看到的是同一份"程序文本"，原始单元序号一致；
  分析把 marker 当成 `EXPLICIT_SYMBOLIC_FAULT` 根，和以前手写的 marker 完全一样。
* **每种故障一个布尔 marker**：规划、compose、FlipQuery、finding 都不用改；
  `IOException` 保留旧名字，其它种类在名字后加类名。
* **种类 = 调用方会区分的环境异常**（读 HDFS 代码得出）：
  * `RetryPolicies.FailoverOnNetworkExceptionRetry`：`ConnectException`、
    `EOFException`、`ConnectTimeoutException` 等一律 failover 重试（不管幂等），
    一般 `IOException` 只有幂等时才重试；
  * `LeaseRenewer`：`SocketTimeoutException` 放弃续租并关闭所有正在写的文件；
  * 因此请求门（请求没发出）= `IOException`、`ConnectTimeoutException`；
    响应门（服务端已执行、响应丢失）= `IOException`、`EOFException`、
    `SocketTimeoutException`；SASL 门在客户端路径上没有区分，只保留 `IOException`。
* **语义异常从不注入**（`StandbyException`、`InvalidToken`、
  `InvalidEncryptionKeyException` …）：它们必须由服务端状态经跨进程因果链产生，
  否则就是假见证（直接在 SASL 门抛 `InvalidEncryptionKeyException` 会"复现"17897，
  却跳过了真正的原因）。
* 九棵 Hadoop 树删除了手写门（各分支本地提交），只重编两个类。

### 1.3 顺带的陷阱（已修）

织入的请求门是 10 个 Jimple 单元（两种故障 × 5），手写门是 5 个，于是
`sendRpcRequest` 里声明过的两个循环 id 各后移 5（`u48→u53`、`u53→u58`，
`bd3b0af5f`）。第一次回归 v52 里 6 个 case 因此在 PLAN 就被拒绝，改完即恢复。

---

## 2. 重放的完善：偏序只用在 CONFIRM（`7f60d2a0d`）

### 2.1 为什么只在 CONFIRM

9 月 24 日的偏序重放实验（v41–v43，4/1/1 of 9）失败于探索阶段的 daemon 漂移。
探索阶段因此保持全序不变；偏序只用于 SAT 之后的验证——那里的问题是"模型给出的
顺序能不能在这个程序里实现"，而实现不了本身就是答案。

### 2.2 设计

```
            录制的全序（探索阶段仍按它走）
  ──e1──e2──e3──WAKE──e4──e5──WAKE──e6──►
                  │               │
CONFIRM：   只有 WAKE 仍"不早于录制"（daemon 不会跑到前面去）；其余事件自由

            模型的偏序（ConfirmMain 从闭包里的每个读写连接导出）
  ┌──────────────────────┐   ORDER    ┌──────────────────────┐
  │ W 的 activation       │──────────►│ R 的 activation       │  写者退出后读者才进入
  │ occ(W) | frames(W)    │  exit→enter│ occ(R) | frames(R)    │
  └──────────────────────┘            └──────────────────────┘
  ┌──────────────────────┐            竞争写者 W'：录制中在 W 之前 → 先于 W；
  │ W' (同一位置的别的写者) │            否则 → R 之后
  └──────────────────────┘
  等待超过 causynth.confirm.order.timeout.ms（默认 300 s）→ CONFIRM_MISMATCH
  "the model orders it after …, which did not exit …, so this program cannot
   realize the model's order" → 结论降级为 SAT_UNCONFIRMED
```

* 粒度就是模型自己的粒度：`Arms` 的一个 STATE arm 是"写者 occurrence 对位置 L
  的最后一次写"；端点的 frames 指出它所在的方法 activation
  （`Endpoint.activation()` 去掉事件帧 `(site,k)`）。
* 门挂在每一遍都已织入的 hook 上（`Identity.enterFrame/exitFrame`、occurrence
  打开、`regionExit`），不需要新的字段 hook，也不改 VM。
* 录制顺序不再保持，所以"钉住的"连接也要检查：闭包里的每个读写连接都写成 STATE 行。
* 同一个 occurrence 里的两个 activation 不建门：它跑在一个线程上，程序顺序已经排好
  它们（第一版漏了这一条，11741 因此被误拒，见 §5.1、§7）。

---

## 3. 新 bug 的寻找

### 3.1 静态调研（13 个候选）

在 trunk（`d57814e3015`）里找"一个节点对来自另一个节点的值做 ad-hoc 检查"的位置。
强候选：

| # | 位置 | 跨节点的值 | 失配场景 |
|---|---|---|---|
| 1 | `NameNodeConnector.checkAndMarkRunning` + `ExternalStoragePolicySatisfier.getNameNodeConnector` | NN 上 id 文件的租约持有者 vs 调用方自己的 client 名 | `create` 的**响应丢失** → 重试时 `append` 撞上自己的租约 → 当成"另一个实例" |
| 2 | `DFSClient` 取 DEK + `DataStreamer` 的 bad-node 逻辑 | NN 给的 DEK 过期时间 vs 客户端时钟；NN RPC 失败被算到 DN 头上 | 取 key 的 **IPC 请求丢失** → 健康 DN 被排除 |
| 3 | `BlockRecoveryWorker`："Inconsistent size of finalized replicas" | 多个 DN 的副本长度 | truncate 恢复第一次尝试中 update/commit 丢失 → 之后每次尝试都抛 |

其余 10 个及判断：

| # | 位置 | 判断 |
|---|---|---|
| 4 | `DataNode.getDataEncryptionKeyFactoryForBlock` 的匿名 factory：`clearDataEncryptionKey()` 是空操作 | 17899/17967 修复里 DN 端"清 key 重试"会用同一个 key 再试一次——值得作为负例验证 |
| 5 | `BlockManager` 发出 KeyUpdateCommand 后 `setNeedKeyUpdate(false)` | 响应丢失后 DN 最多落后一次轮换；预发的"下一个 key"大多盖住（§3.4 的结果印证） |
| 6 | `DiskBalancer` "Executing another plan" / `OLD_PLAN_SUBMITTED` | 提交响应丢失后重交被拒；影响小 |
| 7 | `BlockChecksumHelper` 条带校验遇 ERROR_UNKNOWN_KEY 回退重算 | 只是变慢，结果正确 |
| 8 | `ImageServlet` "recent image" 409 | HTTP、非本工具的门 |
| 9 | `BlockReportLeaseManager.checkLease` | HDFS-16942/17906 已修 |
| 10 | 丢失的 DNA_INVALIDATE | HDFS-17218 已修；同类的 `setBalancerBandwidth(0)` 静默丢失但无检查抛出 |
| 11 | `FsDatasetImpl` "THIS IS NOT SUPPOSED TO HAPPEN" | GS 来自同一 NN 计数器，安全 |
| 12 | IBR 请求丢失 vs `complete()` 副本不足 | `putMissing` 1 s 内重发，安全 |
| 13 | block token 过期、`DelegationTokenRenewer` | 纯时钟偏差，维护者视为范围外 |

### 3.2 候选 #1：已确认的新 bug

`hadoop-hdfs-selflease` 分支 `gc/hdfs-selflease`（`196921fad42`）里的
`TestExternalSpsLostCreateResponse`，4 个测试全过（bug 存在时"通过"）：

* 在客户端重试代理之下替换 protobuf translator：第一次 `create` 真实到达 NN 并被执行
  （fileId 16387），然后抛 `EOFException("simulated lost create response")`；
* 3 秒后重试：`exists` 为真 → `append` → NN：
  `…DFSClient_NONMAPREDUCE_-142238355_1 is already the current lease holder`
  （`AlreadyBeingCreatedException`）→ `checkAndMarkRunning` 返回 null →
  `IOException("Another ExternalStoragePolicySatisfier is running.")` →
  `ExitUtil.terminate(-1)`；
* 打开 `dfs.client.retry.policy.enabled=true` 时，同一 call id 重发，NN 的 retry
  cache 回放响应，SPS 正常启动——默认配置（false，非 HA）下必现；
* Balancer `-asService`：每轮 "Another Balancer is running." 直到 20 分钟租约硬上限。

`git log` 里没有修复；HDFS-16499 引入了这个 terminate，HDFS-13128 是两个不同客户端的情形。

```
  SPS (client c)                         NameNode
  ┌────────────────────┐   create      ┌──────────────────────────────┐
  │ attempt 1          │──────────────►│ /system/mover.id 建立         │
  │ checkAndMarkRunning│   ✗ 响应丢失   │ lease holder = c              │
  └─────────┬──────────┘◄ ─ ─ ─ ─ ─ ─ ─└──────────────┬───────────────┘
            │ EOFException → sleep 3s                    │ 状态保留
  ┌─────────▼──────────┐   exists / append ┌────────────▼───────────────┐
  │ attempt 2 (同一 c) │──────────────────►│ holder == c → ABCE          │
  │ ABCE → return null │◄──────────────────│ "already the current lease  │
  │ "Another … running"│                   │  holder"                    │
  │ terminate(-1)  ✗   │                   └────────────────────────────┘
  └────────────────────┘
```

### 3.3 为什么 GraphChecker 现在找不到 #1

1. **锚点只在错误路径上执行**：`out == null` 的判断在健康录制里走的是另一支，但真正
   出错的是**重试时新出现的 occurrence**（attempt 2）。GraphChecker 要求目标 occurrence
   在种子录制里存在（`ExploreMain.root` 否则 BLOCKING）。——这正是 §4 的 RETRY 模式：
   故障创造了图上原本没有的点。
2. **状态是字符串和异常类型**：租约持有者是字符串，NN 的回答是一个远程异常的类名；
   公式只对原始类型和容器（assoc）建模。
3. **判断没有符号输入**：`out == null` 由 catch 分支决定，是控制依赖而不是数据依赖。

要表达这类 bug，需要"故障创造的 occurrence 也可以当锚点"（先按门逐一注入、观察目标
region 是否出现，再把它定为锚点）——这是本报告建议的下一步，本次没有做。

### 3.4 用 GraphChecker 试一个新检查点：block token 缺 key（case `hdfs-token-key`）

**问题**：key 家族已知的 bug 都在 SASL 的 DEK 查询（`retrieveDataEncryptionKey`）上；
同一个 `allKeys` 还被 block token 校验读（`retrievePassword` 的
`InvalidToken(... required block key (keyID=…) doesn't exist)`，健康路径上每次块操作都执行）。
HDFS-17899 的修复只覆盖 SASL。心跳响应丢失让 DataNode 漏掉 KeyUpdateCommand 时，token 路径
会不会出错？

**做法**：17897 的工作负载与树，在那个 throw 上加 `@CausynthExceptionTarget("hdfs-token-key")`
（`fcaedb3d487`，只重编一个类），锚点是 dn0 上第一次 token 检查
（`REGION.7f08d6f5`，`BlockPoolTokenSecretManager.checkAccess`，`Root:DATA_XCEIVER#1`）。

**两次失败的尝试本身也有信息**：
* t1：把 `DataXceiver` 放进 scope 后，它的 `run()` 成了包住一切的 region，在 SASL 握手确定
  这个连接的因果上下文**之前**就打开了——两个连接落在同一个 Lost 地址上
  （`OCCURRENCE_ADDRESS_SHARED`），组合出的 66 条路径自相矛盾（`PATH_SELF_CONTRADICTORY`）。
  这是身份的一个真实局限（Lost 上下文只能靠时间区分），GraphChecker 正确地拒绝了下结论。
* t3：PLAN 只接受选择器形式（`node/region/REGION.X#k`），不接受渲染出的完整地址。

**结果（v54，全部修复）**：147 个会话、146 次重放走到 token 检查——包括心跳请求 / 响应
丢失的每一种故障——**一次 fatal 都没有**；128 个 valuation 中 11 个可满足但都不需要移动任何根，
结论 `NO_SUPPORTED_WITNESS`，0 个 BLOCKING gap。

**解读**：这是一个有依据的否定结果。NameNode 轮换时把"下一个 key"预先发给 DataNode，
token 用当前 key 签名——DataNode 早在上一次更新里就拿到了它，所以单次 KeyUpdateCommand
丢失碰不到 token 路径；SASL 路径之所以出事，是客户端**缓存**了一个旧的 DEK。
GraphChecker 在这个检查点上没有找到新 bug，这与 HDFS 的设计一致。

---

## 4. 注入故障后因果图的变化

### 4.1 方法

对每个故障重放，把它的 occurrence、WIRE 边（SEND→RECV）、STATE 读写来源、决策、
目标行与种子逐项比较；再减去同一 case 所有非故障重放（时钟、serial 等）也会出现的
变化（"噪声包络"）——否则 11741 的对照重放本身就会因为 balancer 迭代数不同丢掉上百条
消息。脚本：`tools/analysis/graphdiff.py <round>`（输出到 `$GRAPHDIFF_OUT/accept-<round>/`）。

### 4.2 统计（v51：69 个故障重放；v53：114 个，含新故障种类）

| 模式 | 含义 | v51 | v53 |
|---|---|---|---|
| EDGE_CUT | 被故障的交换消失：SEND→RECV、对端处理器 occurrence、搭载的 WIRE 边 | 69/69 | 114/114 |
| RETRY | 同一逻辑调用以新 occurrence / 新 attempt 再出现 | 31 | 60 |
| RECOVERY | 恢复轨迹：新的 region 或别的节点的处理器出现 | 18 | 36 |
| STATE_DIVERGENCE | 某个读改读另一个写者（更新没到达） | 20 | 78* |
| ESCALATION | 失败传到锚点，fatal 被观察到 | 21 | 41 |
| ANCHOR_DROPPED | 锚点那次求值整个消失 | 30 | 22 |
| ABORT | 失败一路抛到工作负载 | 7 | 17 |
| FALLBACK | 改走别的节点 | 4 | 7 |
| TOLERATE | 故障被吞掉，图的其余部分不变 | 6 | 7 |
| 对照组（非故障） | | 90/105 TOLERATE | 46/59 TOLERATE |

\* v53 的 STATE_DIVERGENCE 里有一部分是门自身的 marker 单元：翻带类型的 marker 时，
排在前面的通用 marker 仍被读到（每多一种，`state_gone` 恰好少 2，`repointed` 1→0）。
**这不是 HDFS 的行为**，解读种类差异时要扣除。扣除后，这九个工作负载里新种类引出的
HDFS 行为与通用 `IOException` 基本相同——它们走的路径（DN 心跳、SPS 刷 key、客户端
取 key）都不经过按异常类型分支的 `RetryPolicies`；种类化的价值体现在 HA/failover 代理
和 `LeaseRenewer` 这类路径上，本批工作负载没有覆盖到。

### 4.3 示意图与具体 case

**图 A：健康的因果图（key 家族，17897 的形状）**

```
  NameNode nn0                                   DataNode dn2
 ┌───────────────────────┐   heartbeat REQUEST  ┌──────────────────────────┐
 │ updateKeys            │◄─────────────────────│ BPServiceActor /         │
 │ KEY_MANAGER_TICK      │                      │ 工作负载心跳              │
 └──────────┬────────────┘                      └─────────────▲────────────┘
            │ STATE currentKey/allKeys                         │ RESPONSE
            ▼                                                  │ KeyUpdateCommand
 ┌───────────────────────┐   WIRE keyId, expiry ┌─────────────┴────────────┐
 │ handleHeartbeat →     │─────────────────────►│ addKeys → allKeys.put    │
 │ PBHelper.convert(key) │                      └─────────────┬────────────┘
 └───────────────────────┘                                    │ STATE allKeys
                                                              ▼
                              client            ┌──────────────────────────┐
                        ┌─────────────┐ SASL    │ SASL handler:            │
                        │ checksum op │────────►│ allKeys.get(keyId)==null?│──► 锚点
                        └─────────────┘ WIRE    └──────────────────────────┘
                                         DEK keyId
```

**图 B：请求丢失 → EDGE_CUT + RECOVERY（17897 `93b332cdf32dc8bc-75927b48`）**

```
  dn2 工作负载心跳 ──✗ REQUEST 未发出
      │ 消失：nn0 Anchor:3fec8ffa…（handleHeartbeat）、6 条 KeyUpdateCommand WIRE 边
      │       nn0→dn2（keyId ×3、expiry ×3）、dn2 的 addKeys（REGION.ba3902cd）
      ▼
  NN 的 needKeyUpdate 仍为真  ──►  新出现：nn0 PBHelper.convert（REGION.1330a52b）
                                   上下文 Anchor:…@HADOOP_IPC/BP_SERVICE_ACTOR
                                   = KeyUpdateCommand 改搭 dn2 的下一次 daemon 心跳
```

**图 C：响应丢失 → 状态分叉 → 升级（七个 case 的机制，例：17967-pathC）**

```
  nn0 handleHeartbeat（已执行，needKeyUpdate := false）
      │ RESPONSE ✗ 丢失
      ▼
  dn 的 allKeys 停在旧 key（STATE_DIVERGENCE：锚点的 allKeys.get 改读更早的写）
      │ NN 不会重发（flag 已清）
      ▼
  客户端/上游 DN 拿新 keyId 来握手 → allKeys.get == null → InvalidEncryptionKeyException
  （ESCALATION：v51 中 7/7 个响应丢失会话都观察到 fatal）
```

**图 D：SASL 故障 → FALLBACK / ANCHOR_DROPPED（17897 `ac3675da9079644d-9ecc68a8`、11741 `b58cdceb…`）**

```
  client ──SASL k0..k2──► dn0 （dn0 缺 key：keyID=119994 doesn't exist. Current key: 119992）
     │
     └─SASL k3,k4──► dn1（种子里这个站点从没连过 dn1）   FALLBACK
                      dn1 DATA_XCEIVER 先试 dn0（k0–k4），k6/k7 改连自己
  11741：balancer→dn1 的 req.data-encryption-key-id WIRE 边消失，dn1 的 SASL 处理器
         消失，目标求值 4→3                               ANCHOR_DROPPED
```

**图 E：模式汇总**

```
          ┌──────────── 故障注入在门 d ─────────────┐
          │                                         │
     EDGE_CUT（总是）                              TOLERATE（吞掉）
          │
   ┌──────┼──────────────┬───────────────┐
 RETRY  RECOVERY/FALLBACK STATE_DIVERGENCE ABORT
   │        │                  │
   └────────┴──────► 新 occurrence（种子里没有）
                              │
                   ESCALATION（到锚点，fatal）或 ANCHOR_DROPPED（锚点消失）
```

GraphChecker 对这些变化的捕获：新 occurrence 有稳定身份，读写/决策/跨节点边都写进
会话；落在已规划 region 里的直接进入 compose；种子没到过的 region 由 GROW 补规划
（本批从未触发）；跑在血缘丢失线程上的只能得到 `ROLE.x` 地址——这是盲区。

---

## 5. 九个 case 的回归与因果链

### 5.1 v53（门 + 偏序 CONFIRM，`bd3b0af5f`）

8/8 PASS（17897、17899-bug1/2/3、17960、17967-pathA/B/C），发现与之前相同：七个 IPC 门的
MARKER_FLIPPED、17960 的 `SNAPSHOT_DELETION_ORDERED=false`。见证翻转的仍是**通用
`IOException`**（`sendRpcRequest#u16`；`u21` 是 `ConnectTimeoutException`）——新故障种类
都被探索到了（请求门两种各 34 次、响应门三种各 12 次、SASL 14 次），但没有改变结论。

**11741 暴露了我引入的一个 bug（已修）**：它是九个里唯一真正走 CONFIRM 重放的（跨会话
拼接，17 STATE + 8 WIRE）。ConfirmMain 生成了一条自相矛盾的门：
`ORDER 39dcf5ae|: the model orders it after [39dcf5ae|…removeExpiredKeys()@0]`——
同一个 occurrence 里的嵌套 activation 要先于这个 occurrence 本身，只能超时，于是
`SAT_UNCONFIRMED`（漏报）。修正（`ac85e474f`：同一 occurrence 的两个 activation 不建门，
一个线程的程序顺序已经排好它们）后，用同一轮的环境单独重跑这次 CONFIRM：
**确认**——"every edge the model chose was taken, and the anchor observed the fatal"。
11741 的 5 条 ORDER 正是它的因果链：dn 上转换 KeyUpdateCommand 的 key
（`PBHelper.convertBlockKeys → DelegationKey.<init>`）→ addKeys 所在 occurrence →
SASL 查询（`retrieveDataEncryptionKey`）。

### 5.2 因果链对照（v53 vs v51 基线，`tools/analysis/chaincheck.py <round> [baseline.json]`）

每个 case 的 `.smt` 仍然是：多条路径由 `path_selector` 的 ite 组合、`target_path_partition`
（选择器求和 = 1）、`fatal_target`（选择器的或）、`check-sat`；容器链（`assoc_put`/
`assoc_remove`/`assoc_has`）和跨线的 key（HOFF handoff 符号）都在，NameNode 的
KEY_MANAGER 时钟（`REGION.08ab84c9` 8 个）都在；变化只来自新故障种类：

| case | 路径 | ite | message arm | 请求门根 | 响应门根 | assoc_put |
|---|---|---|---|---|---|---|
| 17897 | 13 → 18 | 473 → 639 | 73 → 109 | 4 → 8 | 3 → 9 | 116 → 160 |
| 17899-bug1 | 13 → 19 | 441 → 596 | 53 → 81 | 5 → 10 | 1 → 3 | 108 → 145 |
| 17899-bug2 | 17 → 32 | 1513 → 3817 | 155 → 383 | 6 → 14 | 2 → 9 | 168 → 316 |
| 17899-bug3 | 12 → 17 | 387 → 488 | 46 → 67 | 3 → 6 | 1 → 3 | 95 → 119 |
| 17967-pathA | 13 → 19 | 441 → 596 | 53 → 81 | 5 → 10 | 1 → 3 | 108 → 145 |
| 17967-pathB | 11 → 17 | 355 → 510 | 41 → 69 | 3 → 8 | 1 → 3 | 90 → 127 |
| 17960 | 3 → 2 | 16 → 14 | 0 | – | – | 0（配置机制，无 IPC 门） |

### 5.3 v54：全部修复后的最终回归（`ac85e474f`，快照 p55）

**9/9 PASS**，全部通过因果锥检查（`accept/cone.py`）：

| case | 结论 | 路径 / ite | 机制 | 确认方式 |
|---|---|---|---|---|
| 11741 | PASS 2432 s | 57 / 6717 | CLOCK_SKEW（NN `updateKeys` 时钟） | **偏序 CONFIRM 重放**：5 ORDER、17 STATE、8 WIRE 全部走到，锚点观察到 fatal |
| 17897 | PASS | 18 / 639 | IPC 请求门 MARKER_FLIPPED | 所选会话本身 |
| 17899-bug1 | PASS | 19 / 596 | IPC 请求门 | 所选会话本身 |
| 17899-bug2 | PASS | 31 / 3751 | IPC 响应门（SPS） | 所选会话本身 |
| 17899-bug3 | PASS | 17 / 488 | IPC 请求门 | 所选会话本身 |
| 17960 | PASS | 2 / 14 | `SNAPSHOT_DELETION_ORDERED=false` | 所选会话本身 |
| 17967-pathA/B/C | PASS | 19/596、17/510、19/596 | IPC 请求门 | 所选会话本身 |

11741 的 `.smt` 仍是那条链：`allKeys` 是 `assoc_put`（530）/`assoc_remove`（42）/
`assoc_has`（62）组成的 ite 容器表达式，NameNode 的 key 经 KeyUpdateCommand 以 handoff 符号
过线，求解器移动的是 NameNode `updateKeys` 的 KEY_MANAGER 时钟。

---

## 6. 验证过滤假阳性的例子

GraphChecker 有两道"拿执行证据否决模型"的关卡：

* **COMPOSE 的录制一致性检查**：一个析取项如果在"所有根都取录制值"时就可满足，而它自己
  的录制走的是健康分支，模型就与执行矛盾——`FORMULA_SAT_AT_RECORDED_VALUATION`，
  BLOCKING，扣下结论；
* **CONFIRM**：种下模型的根值、按模型的偏序重放，要求模型的每条边都被实际走到、锚点观察到
  fatal；实现不了模型的顺序（卡死）、走了别的边、没有 fatal，都判为未确认。

### 6.1 E1：符号化不合理 → SAT 错误 → 被录制证据否决

**做法**：case `hdfs-17897-nowire` = 17897 去掉两条块 key 的 WIRE 映射
（NameNode→DataNode 的 keyId 与 expiry）。这相当于"没有把应该符号化的跨节点值符号化"：
DataNode 收到的 key 在模型里和 NameNode 的符号值断开（过线的 handoff 符号 6 → 2）。

**结果**（`~/gc-out/accept-e1-17897-nowire`）：121 个 valuation 中 11 个 SAT；可满足的
析取项恰恰是**种子录制自己的路径**（`2172fd59ff6bf485`，`seed-result-12df0a51`）——
公式声称"录制的世界就会到达 fatal"，而录制本身是健康的。COMPOSE 判
`FORMULA_SAT_AT_RECORDED_VALUATION`（BLOCKING），结论 `INCONCLUSIVE_PARTIAL`，
`FINAL_REFUSED`，没有任何见证被报告。

**为什么被过滤**：断开映射后，锚点 `allKeys.get(keyId) == null` 读到的 key 集合不再被
NameNode 那边的约束绑定，fatal 条件在录制取值下也能满足；但录制是一次真实执行，它走了健康
分支——模型与真实执行矛盾，所以模型错。对照：完整映射的 17897（v53）同一检查通过，见证
是移动 IPC 请求门的 MARKER_FLIPPED 并被确认。

```
  完整映射（17897）                         去掉映射（E1）
  NN keyId ──WIRE──► DN allKeys             NN keyId ──✗──  DN allKeys（与 NN 断开）
       │                  │                      │                 │
       └──── 同一符号 ─────┘                      └── 公式里无关 ─────┘
  录制取值：allKeys 含 keyId → 健康 ✓        录制取值：fatal 也可满足 ✗ ← 与录制矛盾
  需要移动根（门故障）才到 fatal              → FORMULA_SAT_AT_RECORDED_VALUATION，扣下
```

### 6.2 探索阶段：求解器说"这个翻转可达"，执行说"那个 occurrence 根本不存在"

每个探索义务本身就是一个 SAT 模型（在某个"世界"里翻转某个决策），重放是它的验证。
`hdfs-token-key`（t1）的 119 个义务中 81 个被准入、32 个 UNSAT、**6 个被执行否决**：

* 3 个 "occurrence … never reached `doSaslHandshake#u15` in this replay"。例
  `obligations-0001/55e210569e67e811`：世界里已经种下一个响应门故障
  （`REGION.9ffdee3d…3a5104c6 = true`）和 dn0 上的一个 SASL 门故障
  （`REGION.61e62f41…3b65b017 = true`）；求解器在此基础上要求 occurrence
  `1d2ac92615179627` 走到 SASL 握手并翻转它的门。重放里，上游故障让这次操作提前中止，
  那次握手**根本没有发生**。
* 3 个 "this replay published no root mint row for [响应门 …]"：模型要移动的门事件在
  这个世界里没有出现。

**为什么被过滤**：公式只描述"已存在的 occurrence 走哪条分支"，不描述"某个 occurrence
是否存在"——两个故障互相排斥（前一个让后一个的载体消失）在公式里看不见，只有执行看得见。
这正是 §4 的 EDGE_CUT/ANCHOR_DROPPED 在求解层面的后果。

```
  求解器的世界：  故障 F1（响应丢失） ∧ 在 occurrence X 上翻转 SASL 门
                         │
  执行：            F1 → 操作中止 → X 不存在 ──► "never reached"，义务不准入
```

### 6.3 CONFIRM（SAT 之后）：模型的读写来源顺序实现不了 → 卡死 → 拒绝

九个 case 的公式里没有写者选择（writer arm），8 个结论又都被"所选会话本身就是见证"直接
确认，所以自然运行里偏序 CONFIRM 只作用于 11741。为了看清它能否过滤假阳性，做了一对
**受控**实验（基于 17899-bug1 v53 的真实结论 valuation 5，工具
`tools/analysis/confirmrun.sh` 用该轮 worker 的原环境单独跑一次 CONFIRM 重放，
`tools/analysis/EndpointOf.java` 算端点 id 与 activation；工作目录须在 `~/gc-out` 下，
与种子计划同一文件系统）：

| | 模型 | 结果 |
|---|---|---|
| **E2-control** | 原结论：target-dn 的心跳请求丢失（IPC 请求门 = true），SASL 查询读到的 key 集合里没有客户端的 keyId | **确认**："every edge the model chose was taken, and the anchor observed the fatal"——不保持录制顺序（只有 WAKE 不早于录制）也能实现，真阳性保住 |
| **E2** | 同一个世界，但把锚点那次读（`3c8171373ef7a4b6`，target-dn 的 `retrieveDataEncryptionKey`）的写者换成**种子里 target-dn 的 addKeys**（`b3e178ca83894a2a`，KeyUpdateCommand 送达后写入 allKeys）——相当于求解器把"故障会话的路径"和"健康会话的读写来源"拼在一起 | **拒绝**：`ORDER …retrieveDataEncryptionKey…: the model orders it after [43d4d749…addKeys…], which did not exit within 60000 ms, so this program cannot realize the model's order`；`STATE 3c8171373ef7a4b6: the model joined this read to writer b3e178ca83894a2a (version 967), the run observed MAP/234#-3@1354 written by 259ee051059081eb`；锚点两次求值都没有 fatal |

**为什么被过滤**：这个世界里 target-dn 的心跳请求没发出，NameNode 就不会生成那条
KeyUpdateCommand，target-dn 的 addKeys（锚点所等的写者）**在这个程序里根本不会发生**。
偏序门让读者的 activation 等写者的 activation 退出——等不到，就是"模型要求的读写顺序无法
实现"，按规则判为假阳性；同时读到的也不是模型选的写者。对照组说明门本身不会误伤真见证。

```
  target-dn 心跳 ──✗ REQUEST（本世界的故障）
        │
        └─ NameNode 不产生 KeyUpdateCommand ─► target-dn.addKeys 不会发生
                                                    ▲
  E2 模型：SASL 查询 ◄── 读 addKeys 写入的 allKeys ────┘   ORDER：addKeys 退出 → 查询进入
  执行：查询的 activation 等 60 s，addKeys 从未出现 → ORDER 不可实现 → CONFIRM_MISMATCH → 拒绝
```

---

## 7. 修掉的 GraphChecker bug

| 提交 | bug | 证据 | 修法 |
|---|---|---|---|
| `bd3b0af5f` | 门织入后 `sendRpcRequest` 的循环 id 移位 | v52：6 个 case 在 PLAN 被 `BOUNDED_LOOP_BODY_BOUND_DISAGREES` 拒绝 | 声明的 id 后移 5 |
| `eaf7530b6` | 经反射的写，站点名随 JVM 预热在 `NativeMethodAccessorImpl` 与 `GeneratedMethodAccessorN` 之间变化 | v51 17897 一次重放里 16 个读"看起来改了写者" | 工作负载 JVM 加 `-Dsun.reflect.noInflation=true` |
| `e723281e4` | lineage-only 的 daemon（BPServiceActor）没有帧，归属落到 `unregistered`；窗口号在三个 DN 之间共用，重放间身份漂移 | 17897 种子里 11 个 `unregistered/Root:BP_SERVICE_ACTOR` | 线程开始执行工作对象时（claim 点）把它记为最外层接收者；CausynthCluster 已注册 actor |

| `ac85e474f` | 偏序 CONFIRM 在同一 occurrence 的两个 activation 之间建门（嵌套的要先于外层），只能超时 | v53 11741 `SAT_UNCONFIRMED`：`ORDER 39dcf5ae|… after […removeExpiredKeys()@0] … did not exit within 300000 ms` | 同一 occurrence 不建门；被连接的写者不算自己的竞争者；重跑后确认 |
| `ba3d1530e` | 实验 case 混进默认轮次 | v54 一次多启动了两个实验 | 实验只在 `CASES` 点名时启动 |

偏序 CONFIRM 的一个已知缺口：查询时 VM 为容器视图当场产生新版本（17899-bug1：
`retrieveDataEncryptionKey#74` 的 MAP 视图），这时 addKeys 对 map 的写不是一条直接连接，
ORDER 推不出来，只能靠 fatal 检查兜底（11741 里这条链是直接连接，已被 ORDER 覆盖）。

已知的偶发测试：`OccurrenceAddressIsNotARequestTest` 在整套测试 + 高负载时偶尔失败，
单独跑 12/12 通过——与测试顺序有关，未深挖。

未修、只记录的：块 key 的 WIRE 映射也匹配 `DatanodeRegistration.exportedKeys`
（DN→NN，NN 不读），带来 64–79% 的未配对导出和多余的消息 arm——改它会动九个 case
的映射，留待单独验证。

---

## 8. 限制与下一步

1. 错误路径上的锚点（§3.3）：让故障创造的 occurrence 可以成为锚点。
2. 字符串 / 异常类型状态进入公式。
3. 种类化故障在 HA/failover 与 `LeaseRenewer` 路径上的工作负载。
4. 映射过匹配（§7）。
