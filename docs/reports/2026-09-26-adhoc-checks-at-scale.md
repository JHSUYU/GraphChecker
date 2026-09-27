# GraphChecker 在 HDFS ad-hoc 检查上的大规模运行（2026-09-26）

姊妹报告：[`2026-09-26-fault-injection-and-validation.md`](2026-09-26-fault-injection-and-validation.md)
（门的设计、偏序 CONFIRM、九个 case 的图变化）。本报告只讲新任务：在我自己找到的
HDFS ad-hoc 协调检查上真实地、大规模地跑 GraphChecker，用故障注入的设计总结它们，
并在这些检查上给出**真实运行里**出现的假阳性过滤例子（不构造）。

## 0. 结论摘要

| 项 | 结果 |
|---|---|
| 规模 | 21 个 ad-hoc 检查（覆盖率找出，全部注解在一棵 JDK 8 树上）、31 个 case、6 个已有单元测试作工作负载；轮次 a4（30 个 case）+ a5（10 个重跑）+ a6（4 个）+ a7（1 个）；a4 里 **261 个故障重放** + 49 个对照重放 |
| 设计 | 根按类别自动识别（CLOCK / FAULT / READ），不再手写 `symbolic-inputs.jsonl`；具体值判定的 target 有了三条通用规则（helper 返回常量由其分支决定、析取守卫取各测试致命臂的或、健康的具体判定以 DIAGNOSTIC 排除）；wire 流自动配对已设计（§8） |
| 结果 | 时钟类检查 token-expired.proxy / .mirror、token-pw-expired.mirror 得到 **CLOCK_SKEW，并由 CONFIRM 重放确认**（a6、a7；是 HDFS 时钟大致同步的设计前提，不是新 bug，§5.4）；其余具体值检查以"没有被建模的根能到达致命臂"结束——a4 的 261 个故障重放里 83 个到达检查，a5 三个 flush case 的约 1700 个 session 里检查到达 4000 余次，**致命臂 0 次**（§3、§4） |
| 假阳性过滤（全部来自真实运行） | §5：公式在录制取值下可满足 ×6（sender-gs、token-expired、commit-gs、lease-holder）；探索中模型可行、执行否决 68 次（两个故障不独立、门没经过、根只存在于故障世界）；**跨运行拼接的消息配对**（token-nokey.mirror / .replicate：只有把一次运行的状态配上另一次运行 NN 下发的 key 列表才会失败，每次运行自己的配对下 UNSAT，DECIDE 不命名机制、不发布）。CONFIRM 的偏序关卡在真实运行里**没有**触发过（§5.4） |
| 集群单测当工作负载 | 301 个测试的清单；20 对（检查 × 测试）里 18 对在窗口内到达检查；18 个 campaign 首跑 11 个种子重放复现失败，逐个找出 3 类分歧并修掉（推迟的 RPC 响应、HA 随机选 NN、排队区域的帧），修后种子重放 88–89/94；致命臂 0 次，新 bug 0 个；过滤实例：执行否决 178 个模型、59 条自相矛盾路径被扣下（§9） |
| 九个 case | v58（p62）**9/9 PASS**，因果链与 v54 一致或更丰富；11741 CLOCK_SKEW 由 CONFIRM 重放确认 |
| 修掉的引擎缺陷 | 15 个，另有 1 处工作负载登记修复，都在 adhoc 运行里暴露（§6） |

---

## 1. 检查点从哪里来

**ad-hoc 协调检查**：一个 `throw`，它的守卫比较"本节点持有的值"和"另一个节点发来的值"，
而且某个已有单元测试的健康路径会求值这个守卫并通过（守卫行被执行，`throw` 行没有）。

找法（`tools/analysis/`）：

```
throwsites.py   ──►  coverage.sh (JaCoCo, 纯 JDK 8)  ──►  reached.py
 列出三个模块里        每个工作负载跑一遍，                守卫行被覆盖、throw 行未被覆盖
 所有显式 throw        得到 class/line 覆盖                 的 throw = 候选检查点
```

最终 21 个检查（`experiments/hadoop/adhoc/checks.tsv`），都在一棵 JDK 8 树
`~/hadoop-hdfs-17967-c`（分支 `gc/hdfs-17967-pathC`）上；`mkadhoc.py` 在 throw 所在行
插入全限定名注解（不移动行号）并写 `targets/`：

| 检查 | 位置 | 守卫（节点间比较的两边） | 工作负载 |
|---|---|---|---|
| token-blockid | BlockTokenSecretManager:384 | token 里的 blockId ≠ 请求的 blockId | mirror proxy |
| token-expired | BlockTokenSecretManager:388 | `isExpired(token.expiryDate)`（NN 的时钟 vs DN 的时钟） | mirror proxy |
| token-password | BlockTokenSecretManager:441 | DN 重算的密码 ≠ token 带的密码 | mirror |
| token-pw-expired | BlockTokenSecretManager:533 | 同上路径上的过期检查 | mirror |
| token-nokey | BlockTokenSecretManager:541 | DN 找不到 token 的 keyId（NN 轮换 key vs DN 的 key 集合） | mirror replicate |
| sender-gs | BlockSender:275 | 副本 GS < 请求的 GS | mirror reconstruct flush |
| recv-offset | BlockReceiver:564 | 包头 offset > 副本已有字节数 | mirror flush |
| finalize-gs | FsDatasetImpl:2049 | 已有副本 GS > 要 finalize 的 GS | mirror flush |
| visible-gs | FsDatasetImpl:3274 | 副本 GS < 客户端给的 GS | flush |
| reader-chunk | BlockReaderRemote:432 | DN 回的首 chunk offset 与请求 offset 不符 | reconstruct flush |
| reader-header | BlockReaderRemote:197 | DN 回的包头 seqno/长度不合法 | flush |
| commit-gs | BlockManager:1192 | NN 的 GS ≠ 客户端 commit 的 GS | flush softlimit |
| commit-blockid | BlockInfo:444 | NN 的 blockId ≠ commit 的 blockId | flush |
| complete-uncommitted | BlockManager:1308 | 最后一块不是 COMMITTED | flush |
| lease-holder | FSNamesystem:3250 | 文件的租约持有者 ≠ 调用者 | flush softlimit |
| lease-missing | FSNamesystem:2968 | 调用者没有租约 | softlimit |
| addblock-notreplicated | FSDirWriteFileOp:183 | 上一块副本数不够 | softlimit |
| close-retries | DFSOutputStream:1014 | `complete()` 重试次数耗尽 | softlimit |
| ack-seqno | DataStreamer:1262 | DN 回的 ack seqno ≠ 客户端期待的 | flush |
| stream-offset | DataStreamer:765 | 包的块内末尾偏移 > 块大小 | flush |
| pipeline-reply | DataStreamer:1223 | 某个 DN 的回复不是 SUCCESS | flush |

一个 case = `<检查>.<工作负载>`，共 **31 个**。工作负载都是已有单元测试：
四个 block-key 族的传输测试（mirror / proxy / replicate / reconstruct），和上游
`TestFileAppend#testSimpleFlush`（flush）、`#testAppendAfterSoftLimit`（softlimit），
只加了节点登记与录制窗口（`CausynthCluster.registerCluster` + `startRecording`）。

**一个检查被删掉（recv-seqno）**：覆盖率统计的是整个 JVM，包括录制窗口**之前**的准备。
BlockReceiver 的 PacketResponder seqno 检查只在 mirror 测试开窗前的那次客户端写里跑过；
窗口里是 DataNode 之间的 `transferBlock`（`isClient=false`），根本不启动 PacketResponder。
GraphChecker 在 SEED 报"没有观察到异常上下文的激活"是对的——只有发现运行才能说明
窗口内到没到这个检查。

**target occurrence 的发现**：每个 case 先跑一次"发现运行"（occurrence 留空），PLAN 以
`DECLARED_TARGET_OCCURRENCE_MISSING` 拒绝并列出观察到的所有 target occurrence，
`tools/analysis/occurrences.py` 从日志取选择子 `node#epoch0/region/REGION.<id>#k`
（mirror 类取 mirror-dn，proxy 类取 proxy-dn，与同族一致）。30 个 case 已登记；
visible-gs.flush 的 target 在 DataNode 的 IPC 服务端运行，工作负载没把 DN 的 RPC server
登记为该节点，地址落在 `workload/unregistered`，要修工作负载后再跑。

## 2. 根的自动识别与传播边界（本轮的设计改动）

老板的要求："symbolic-inputs 其实可以自动化选择，本质就是那几类；传播边界也自动化。"
以前每个 case 手写 `symbolic-inputs.jsonl`（方法行、字段行、配置源），对 31 个新 case
不可行。现在按**类别**从程序文本识别根（GreyGraph §3.1：输入由分析推导，不靠声明）：

| 类别 | 识别规则 | 实现 |
|---|---|---|
| CLOCK | JVM 时钟（`currentTimeMillis`/`nanoTime`），或无参、每个返回值都是时钟经常数运算得到的方法（从方法体读，库和应用一样）：Hadoop 的 `Time.now`、`Time.monotonicNow`、`Timer.now` 自动被认出 | `causynth/RootCatalog` |
| FAULT | 门织入的 marker（`DoorWeave`） | 已有 |
| READ | 读"织入版本化不了"的访问器（在织入程序之外执行，例如 `AtomicInteger.get`）且该位置被另一个 region 写过：发一个占位读，闭包把它连到写者 | `StaticScopeMap` `inputKind=READ`，按**站点**准入 |

静态作用域图（`static_scope_map.jsonl`）给每个 `DECLARED_SITE` 标 `inputKind`；
finalizer 和 PLAN 只读这张图，不再读任何 case 文件。删掉了 `DeclaredSymbolicInputs`、
方法行、`DECLARED_INPUT_ENTRY` 等整套声明机制和每个 case 的 `symbolic-inputs.jsonl`。

**具体值判定的 target**：很多 ad-hoc 检查比较的是具体值（GS、blockId、seqno…）。
一类可以自动变成符号的：守卫测试一个 helper 返回的 0/1 常量，而 helper 的返回值是它
**唯一一个分支**物化出来的（`return now > expiry;` 编译成两个分别返回 1/0 的臂）。
`causynth/BooleanReturns` 在静态图里把这种守卫的"决定者"记为 helper 的那个分支
（`guardDeciders`），target 行就站在 helper 那次判定的事件上（token-expired 的
`isExpired` 就是这样变成符号的）。其余具体值判定的 target：观察到致命臂时 phi 为真，
否则这条路径**以 DIAGNOSTIC 排除**（没有任何根能让它到达致命臂），不再作为析取项。

**传播边界**：WIRE_FLOW（protobuf 字段 setter→getter）目前仍是 block-key 族手写的
几行；adhoc 检查比较的 GS / blockId / seqno / offset 既不在 wire 流里，其源头（NN 的计数器）
也不是根。所以这些检查在单次运行里总是具体值判定，**只能靠故障改变控制流、在故障
session 里直接观察到致命臂**来得到 witness（§4）。wire 流的自动配对是下一步（§8）。

## 3. 大规模运行

| 轮 | 快照 | case | 说明 |
|---|---|---|---|
| a4 | p64 | 30 | 全部 ad-hoc case 的第一轮；暴露的引擎缺陷见 §6 |
| a5 | p65 | 10 | 修掉 IMPORT 不变量、时钟边界、模型世界等缺陷后重跑；3 个 flush case 在第 3–4 波因义务数翻倍增长被我停掉 |
| a6 | p66 | 4 | CONFIRM 带 `ClockMargin` 与最近世界规则后重跑时钟类 case |
| a7 | p67 | 1 | CONFIRM 在 target 处截断 anchor 的读之后重跑 token-pw-expired |

每个 case 取最后一轮的结果（义务列：被接纳 / 执行未接纳 / 求解器 UNSAT）：

| case | 轮 | 路径 | 义务 接纳/拒绝/UNSAT | 结论 |
|---|---|---|---|---|
| ack-seqno.flush | a5 | — | 103/285/330 | 停止于第 4 波（1080 个待跑义务）：709 个 session，检查到达 1505 次，致命臂 0 次（§7） |
| addblock-notreplicated.softlimit | a4 | 0 | 5/0/0 | 所有路径都是健康臂上的具体判定：没有被建模的根能到达致命臂 |
| close-retries.softlimit | a4 | 0 | 15/0/1 | 所有路径都是健康臂上的具体判定：没有被建模的根能到达致命臂 |
| commit-blockid.flush | a4 | 0 | 17/3/1 | 所有路径都是健康臂上的具体判定：没有被建模的根能到达致命臂 |
| commit-gs.flush | a4 | 0 | 18/3/1 | 所有路径都是健康臂上的具体判定：没有被建模的根能到达致命臂 |
| commit-gs.softlimit | a4 | 0 | 10/0/1 | 所有路径都是健康臂上的具体判定：没有被建模的根能到达致命臂 |
| complete-uncommitted.flush | a5 | 0 | 2/0/0 | 所有路径都是健康臂上的具体判定：没有被建模的根能到达致命臂 |
| finalize-gs.flush | a4 | 0 | 0/0/0 | 所有路径都是健康臂上的具体判定：没有被建模的根能到达致命臂 |
| finalize-gs.mirror | a4 | 0 | 0/0/0 | 所有路径都是健康臂上的具体判定：没有被建模的根能到达致命臂 |
| lease-holder.flush | a4 | 0 | 5/0/0 | 所有路径都是健康臂上的具体判定：没有被建模的根能到达致命臂 |
| lease-holder.softlimit | a4 | 0 | 5/0/0 | 所有路径都是健康臂上的具体判定：没有被建模的根能到达致命臂 |
| lease-missing.softlimit | a4 | 0 | 2/0/0 | 所有路径都是健康臂上的具体判定：没有被建模的根能到达致命臂 |
| pipeline-reply.flush | a5 | — | 81/228/251 | 停止于第 4 波（894 个待跑义务）：697 个 session，检查到达 2069 次，致命臂 0 次（§7） |
| reader-chunk.flush | a5 | — | 76/40/1 | 停止于第 3 波（541 个待跑义务）：334 个 session，检查到达 452 次，致命臂 0 次（§7） |
| reader-chunk.reconstruct | a5 | 0 | 1/0/0 | 所有路径都是健康臂上的具体判定：没有被建模的根能到达致命臂 |
| reader-header.flush | a5 | — | 0/0/0 | 种子重放没复现工作负载（flush 在全序重放下超时，§7） |
| recv-offset.flush | a4 | 0 | 0/0/0 | 所有路径都是健康臂上的具体判定：没有被建模的根能到达致命臂 |
| recv-offset.mirror | a5 | 0 | 0/0/0 | 所有路径都是健康臂上的具体判定：没有被建模的根能到达致命臂 |
| sender-gs.flush | a5 | — | 0/0/0 | 种子重放没复现工作负载（flush 在全序重放下超时，§7） |
| sender-gs.mirror | a4 | 0 | 0/0/0 | 所有路径都是健康臂上的具体判定：没有被建模的根能到达致命臂 |
| sender-gs.reconstruct | a4 | 0 | 0/0/0 | 所有路径都是健康臂上的具体判定：没有被建模的根能到达致命臂 |
| stream-offset.flush | a4 | 0 | 14/37/23 | 所有路径都是健康臂上的具体判定：没有被建模的根能到达致命臂 |
| token-blockid.mirror | a4 | 0 | 0/0/0 | 所有路径都是健康臂上的具体判定：没有被建模的根能到达致命臂 |
| token-blockid.proxy | a4 | 0 | 0/0/0 | 所有路径都是健康臂上的具体判定：没有被建模的根能到达致命臂 |
| token-expired.mirror | a6 | 1 | 0/0/0 | **CLOCK_SKEW，CONFIRM 重放确认** |
| token-expired.proxy | a6 | 1 | 0/0/0 | **CLOCK_SKEW，CONFIRM 重放确认** |
| token-nokey.mirror | a4 | 43 | 129/21/64 | SAT 只来自跨运行拼接的配对，无机制可命名，不发布（§5.5） |
| token-nokey.replicate | a4 | 64 | 93/4/45 | SAT 只来自跨运行拼接的配对，无机制可命名，不发布（§5.5） |
| token-password.mirror | a4 | 0 | 4/0/0 | 所有路径都是健康臂上的具体判定：没有被建模的根能到达致命臂 |
| token-pw-expired.mirror | a7 | 1 | 1/0/0 | **CLOCK_SKEW，CONFIRM 重放确认** |
| visible-gs.flush | a6 | — | 0/0/0 | 种子重放没复现工作负载（flush 在全序重放下超时，§7） |

## 4. 故障注入在这些检查上造成的图变化

方法同姊妹报告 §4：`tools/analysis/graphdiff.py a4`（本轮改为自动发现轮次里的 case，
并认得 DataTransfer 的 SEND 门）。每个被接纳的故障重放都和种子逐层对比（occurrence、
WIRE 边、STATE 边、判定、消息），扣掉对照组（时钟、序号等非故障世界）的噪声后归类。

**a4：13 个 case、261 个故障重放（另 49 个对照重放）**

| 门（故障种类） | 重放数 |
|---|---|
| IPC 请求 `IOException` / `ConnectTimeoutException` | 74 / 37 |
| IPC 响应 `IOException` / `EOFException` / `SocketTimeoutException` | 37 / 32 / 31 |
| SASL 请求 `IOException` | 15 |
| DataTransfer 发送 `IOException` | 8 |
| 两个门同时（嵌套世界） | 26 |

| 模式 | 次数 | 含义 |
|---|---|---|
| EDGE_CUT | 247 | 被注入的那次交换在图上断开（请求没到、响应没回） |
| ABORT | 178 | 发起方收到异常，操作放弃，下游 occurrence 整片消失 |
| STATE_DIVERGENCE | 154 | 共享状态的读写来源变了（例如 NN 执行了请求但客户端没收到响应） |
| RETRY | 63 | 同一请求被重发（`completeFile` 循环、DataStreamer 的流水线恢复） |
| TOLERATE | 24 | 故障被吸收，图的其余部分与种子一致（DataTransfer 发送失败后流水线换节点） |
| ANCHOR_DROPPED | 8 | 目标 occurrence 的锚（产生它的那条消息）不再存在 |

**261 个故障重放里有 83 个到达了目标检查，致命臂 0 次。**

```
          种子（健康）                               注入 IPC 响应故障（close-retries.softlimit）
 client1                  nn0                  client1                  nn0
 ┌───────────────┐ complete() ┌──────────┐     ┌───────────────┐ complete() ┌──────────┐
 │ completeFile  │───────────►│ complete │     │ completeFile  │───────────►│ complete │ 已执行
 │               │◄───────────│ → false  │     │               │  ✗ 响应丢失 └──────────┘
 │ 检查 retries==0│   false    └──────────┘     │ 注入的异常越过 │
 │ (5，通过)      │                            │ 重试循环和检查 │
 │ sleep, 重发    │ complete() ┌──────────┐     │ close() 失败   │
 │               │───────────►│ → true   │     └───────────────┘
 └───────────────┘◄───────────└──────────┘
      EDGE_CUT（响应边断开）+ ABORT（下游消失）+ STATE_DIVERGENCE（NN 已完成、客户端不知道）
```

这个检查要失败，需要 `complete()` 一再**正常返回 false**（NN 认为最后一块副本不够）。
这是服务端的语义应答，按门的设计永远不注入（姊妹报告 §1.2：语义结果必须来自因果链）；
传输故障只会让调用以异常结束，异常越过了重试循环。其余检查也是同样的形状：
故障不是让检查"判错"，而是让到达检查的那条路断掉，或者被重试和流水线恢复吸收。

两个对照值得一提：

* **DataTransfer 发送门（8 个重放，4 个 TOLERATE）**：`Sender.send` 失败后，客户端的
  DataStreamer 把这个 DataNode 标成坏节点、重建流水线，目标检查照常在新流水线上
  执行并通过。
* **嵌套世界里的两个故障（26 个）**：父世界的故障改变了后续流程，子故障往往落在
  "已经不存在"的交换上（§5.2 的第一个例子就是这样被执行否决的）。

## 5. 真实运行里的假阳性过滤

下面的例子全部来自这些 adhoc 检查上的真实运行（证据存档在 `~/gc-out/evidence/`），
没有一个是构造的。按过滤发生的阶段排列。

### 5.1 COMPOSE/DECIDE：公式在"录制取值"下就可满足 → 拒绝（6 次）

| 运行 | case | 检查 |
|---|---|---|
| a1、a2 | sender-gs.mirror | `replica.getGenerationStamp() < block.getGenerationStamp()` |
| a1、a2 | token-expired.proxy | `isExpired(id.getExpiryDate())` |
| a2 | commit-gs.flush | `block.getGenerationStamp() != commitBlock.getGenerationStamp()` |
| a2 | lease-holder.softlimit | `holder != null && !owner.equals(holder)` |

四个检查在录制里都是**具体值判定、走健康臂**，于是 target 行的 phi 为空。当时的 Composer 把
空 phi 当成"没有条件"，这条路径的致命谓词就成了 `(=> selector true)`：公式声称
"这条路径就是失败"。求解器当然给出 SAT，而且不需要移动任何根。

`FORMULA_SAT_AT_RECORDED_VALUATION` 把**每个声明的根都钉在录制值**再问一次：公式仍然
可满足，但它自己的录制走的是健康臂。公式在录制发生的那个世界里说"会失败"，而录制说
"没失败"，所以错的是公式，不是系统。这条 BLOCKING 缺口让四个 case 都停在
`NO_SUPPORTED_WITNESS`，没有发布任何 witness。

没有这个过滤，GraphChecker 会在四个健康的检查上报出"不用任何故障或时钟偏移就会失败"的
假见证。根因（Composer 的空 phi 缺口）随后修掉（`94a50ac3c`），同样的四个检查现在以
"所有路径都是具体健康判定"的 DIAGNOSTIC 结束。

### 5.2 EXPLORE：求解器说"这个故障世界可达"，执行说"不可达"

探索阶段每个义务先由求解器判定"翻转可行"，再真实重放。重放实现不了那个世界的，
以 NOT_ADMITTED 拒绝，不进入语料。a4 里的真实拒绝：

* **两个故障不独立（token-nokey.mirror，4 次"occurrence 从未到达要翻转的判定"）**。
  父世界在 head-dn 的 `heartbeat#1` RPC 请求上注入 `IOException`（已接纳）。子义务再要求
  在 source-dn 的 `heartbeat#1` 请求上注入故障：模型沿用录制里"source-dn 会发这次心跳"的
  路径条件，判 SAT。重放里 source-dn 的心跳根本没发出：工作负载的
  `for (node : nodes) refreshKeysFromNameNode(node, "heartbeat")` 不捕获异常，head-dn 的
  失败中止了循环。模型把两个 occurrence 当成独立的，执行否决了这个组合。
* **门没有经过（commit-gs.flush、commit-blockid.flush、token-nokey.*，20 次"重放没有
  mint 义务要移动的根"）**：模型要翻转的 IPC 门 marker，在重放的那条路径上没被经过。
* **根只在故障世界里存在（stream-offset.flush 37 次、token-nokey.mirror 7 次 `ASSIGNMENT_UNMINTABLE`）**：模型在
  嵌套世界里给一个只由父故障派生出来的重试 RPC 的门赋值；种子录制里没有这个 mint，
  没有 occurrence 可以聚焦植入，在重放之前就拒绝。

### 5.3 DECIDE 的自检：公式在任何世界都为假 → 不当作"反驳"

v56 的 11741 和 a3 的 token-nokey.mirror：`PATH_SELF_CONTRADICTORY` 发现**所有**组合路径
在根全部自由时都不可满足（key map 里只有 put，没有 removeExpiredKeys 的删除分支）。
如果把这当成结论，就是"没有任何世界能失败"的错误反驳。自检把它标成 BLOCKING：
"这是公式的问题，不是录制的事实"。根因是我放宽的服务循环规则（`2144930f8` 修复）。
这一例过滤的是假阴性，与假阳性对称。

### 5.4 CONFIRM：没复现就不发布（token-expired，a4 → a5 → a6）

DECIDE 在 token-expired.proxy / .mirror 上给出 CLOCK_SKEW：把 DataNode 在 `checkAccess` 里
读的时钟拨过 token 的过期时间，`isExpired` 为真，`InvalidToken` 抛出。录制时钟下公式不可
满足（录制能反驳失败），所以这是一个"只要时钟偏"的候选。它经历了三次 CONFIRM：

| 轮 | CONFIRM 植入 | 重放结果 | 结论 |
|---|---|---|---|
| a4 | 没有植入任何时钟（CONFIRM 只重放所选 session 自己的世界） | 健康 | `SAT_UNCONFIRMED`，不发布 |
| a5 | proxy-dn 的时钟 +58354 ms（模型给的最小越界量） | token 过期时间比读数晚 58424 ms，差 **70 ms** 没越界 | `SAT_UNCONFIRMED`，不发布 |
| a6 | +118411 ms（最小越界量 + `ClockMargin` 60 s） | DataNode 以"token 已过期"拒绝 | **`SAT_CANDIDATE`，确认** |

前两次都是 CONFIRM 的缺陷（`e0f30d309`、`32eb30e0c`），而 CONFIRM 的态度是对的：没在
真实重放里看到致命臂，就不发布。这正是"验证过滤假阳性"的另一面：它宁可漏报一个
真机制，也不发布自己没复现的东西。修好之后，同一个候选被真实重放确认。

token-pw-expired.mirror（同一机制，检查在 `retrievePassword` 开头）在 a6 又被 CONFIRM
拒绝了一次，理由是**状态版本边**：

> the run took an edge the model did not choose: STATE dadbafc4c8aa7c11: the model joined
> this read to writer f42a7dde871ffdc4 (version 573), the run never read here

这个读是 mirror-dn 的 `allKeys.get(keyId)`（`MAP/107`），写者是 addKeys 放入这把 key 的
那次写（版本 573）。重放里致命臂**已经出现**了：时钟偏移后，`retrievePassword` 开头的
过期检查抛出，后面的 key 查找根本没执行。可 CONFIRM 把 anchor 的**所有**读都当作必须
走过的边（它沿用了 Composer 的闭包：Composer 把 anchor 的读都当作输入来绑定），包括
target 之后的读。这是 CONFIRM 的缺陷（`4b9ca100a`：anchor 也在 target 处截断），a7 重跑。

**这三次拒绝都不是被过滤掉的假阳性，而是 CONFIRM 自己的缺陷**，修好后同一机制被确认。
所有保留下来的真实运行里（a4–a7 的 adhoc、v58 的九个 case），CONFIRM 没有一次因为
"共享字段的读写来源在偏序下实现不了"而卡住或拒绝（没有 ORDER 超时，没有
`CONFIRM_MISMATCH`）。原因是：会用到"非录制写者版本"的候选在 DECIDE 就被拦下了
（§5.5），走到 CONFIRM 的都是单个 session 自己的时钟偏移，读写来源就是那次运行录下的，
偏序按构造可以满足。偏序关卡要真正起作用，需要一个 STATE_PAIRING_FLIPPED 候选
（某个读取了非录制写者的版本），这批检查没有产生。姊妹报告 §6.3 的 E2 是构造的，不计入。

这个机制是否"是 bug"：DataNode 用自己的时钟判断 NameNode 按 NameNode 时钟写入的过期
时间。测试把 token 有效期设成 1 分钟，所以约 2 分钟的时钟偏差就触发；默认 10 小时的
有效期需要超过 10 小时的偏差。它是 HDFS"时钟大致同步"的设计前提，不是新 bug，但正是
这类跨节点 ad-hoc 检查所依赖、而运维上常被违反的前提。

### 5.5 版本/配对选择引入的假阳性：在 DECIDE 被拦（token-nokey.mirror / .replicate，a4）

老板的判断——"shared field version 共享肯定能引入 false positive"——在这个真实运行里
原样出现了。组合公式为每个读（STATE 家族）和每个接收（MESSAGE 家族）提供**所有**
被录制过的来源作为备选臂：一个读可以取任何一次运行里任何写者写的版本，一个接收
可以取任何一次运行里生产者发出的那条消息。这正是跨运行组合能力的来源，也是假阳性
的来源。

检查：mirror-dn 上 `BlockTokenSecretManager` 找不到 token 的 keyId（`key == null`）。
43 条路径、128 个估值全部判定，其中估值 0、23、24、72、73 为 SAT。离线复现同一份语料
（`tools/analysis/PairingProbe.java`，调用的就是 ClaimPolicy 自己的求解）：

| 固定什么 | 结果 | 模型 |
|---|---|---|
| 什么都不固定 | SAT | NN 的 4 个 KEY_MANAGER_TICK 时钟拨快约 3 小时、mirror 的时钟拨快约 10 分钟，**并且** mirror 接收的 key 列表取自另一次运行 |
| 只固定时钟（W1） | SAT | 时钟世界 `220f0476`（NN 第 1 次 tick 的 removeExpiredKeys 走了另一臂）里的 mirror，接收的却是**种子录制**里 NN 在心跳响应中下发的 key 列表（3 把 key 的 `block-key-id`/`block-key-expiry-date`，6 个叶子） |
| 只固定每条路径自己运行里的配对（W2） | **UNSAT** | — |
| 两者都固定 | UNSAT | — |

W2 不可满足说明：43 条路径所代表的每一次真实运行里，按它自己实际读到的版本和
收到的消息，这个检查都不可能失败。能失败的只有"拼接世界"——一个运行里的节点状态
配上另一个运行里的消息。NN 在世界 `220f0476` 里持有的 key 集合和种子不同，mirror 在
那个世界里不可能收到种子的 key 列表。

过滤发生在 DECIDE：ClaimPolicy 只在失败能归因于一个**录制可以裁决**的机制时才发布
witness（移动的根、时钟，或者单独一处读/接收的配对：钉住它就 UNSAT）。这里的每个
SAT 模型都有别的配对能替代，钉住任何单一机制仍然 SAT，于是没有机制可命名，
结论 `NO_SUPPORTED_WITNESS`，没有 witness 进入 CONFIRM。token-nokey.replicate 同样如此
（7 个 SAT 估值，同样被拦下）。

这一轮还暴露了一个报告缺陷：结论理由写的是"求解器留下了未判定的估值"，实际上 128 个
估值全部判定，缺的是机制。已改为如实说明（`d0502c653`）。

## 6. 这次大规模运行暴露并修掉的 GraphChecker 缺陷

| 提交 | 缺陷（在哪个 case 暴露） | 修法 |
|---|---|---|
| `21cde8990` | `TimedWaits.poll(0)` 从不真正 poll，SynchronousQueue 挂死（flush） | 超时 ≤ 0 直接调 JDK，不发 WAKE |
| `ac780ec8c` | 构造器里的 target 没有 region（sender-gs） | 无外层时构造器自成 region |
| `f44bcc36d` | 根靠手写声明；三个阶段对"到达 target"的定义不一致（lease-holder 报 `UNSUPPORTED_AMBIGUOUS_TARGET_PATH`） | 根按类别识别；到达 = 观察到 TARGET_SITE 的决定性守卫 |
| `2b22d01e2` → `94a50ac3c` | 具体值判定的 target phi 为空，被当成 `true`（sender-gs、token-expired、lease-holder、commit-gs：FORMULA_SAT 拦下，§5.1）；改成 `false` 后又触发 PATH_SELF_CONTRADICTORY | 观察到致命臂 = `true`；健康臂 = 路径以 DIAGNOSTIC 排除 |
| `e6672605c`、`bfb52f3b4` | `isExpired` 这类 helper 返回常量的守卫永远是具体值（token-expired） | helper 分支作决定者；target 行站在 helper 判定处，前缀在它之前截断 |
| `2144930f8` | 我为 17960 放宽的服务循环规则让 11741 的 `addKeys` 从拷贝循环开始，`removeExpiredKeys` 出了 region，v56 的 11741 56 条路径全部惰性 | 服务循环 = root 方法**第一个进入 region 的调用**所在的循环 |
| `b221e451b` | 循环体根共享一个地址、循环里的门重复 mint，同一陈述写了多次，IMPORT 以 invariant 4/8 拒绝（ack-seqno、close-retries） | 发布器按契约键合并**完全相同**的重复陈述，不同的照写 |
| `dfe4cf849` | z3 优化器遇到量词先打印 WARNING，驱动把它当结论：11741 的 101 个翻转被记成"未判定"（重解后 51 个 unsat、19 个 unknown） | 驱动丢弃 z3 的 WARNING 行 |
| `13dba81e2` | 循环体里同一时钟站点反复读取，同一个符号背两个读数（ack-seqno、pipeline-reply，IMPORT invariant 8） | 时钟根 = 该站点在 occurrence 里的第一次读数，之后的读数按植入值运行、保持具体 |
| `743b854af` | 两个 occurrence 在同一个"最后 VM 事件"之后做具体判定，target 行 seq 相同（recv-offset.mirror，invariant 4） | 键里加入 occurrence |
| `12ff25587` | `a \|\| b \|\| c` 的守卫对每个测试都直接控制依赖，PLAN 当作歧义拒绝（reader-chunk） | 析取守卫：phi = 各测试致命臂的"或"，target 站在第一个测试 |
| `e0f30d309` | CONFIRM 只重放所选 session 自己的世界，模型放开的时钟没有植入（token-expired ×3：SAT_UNCONFIRMED） | CONFIRM 在该世界上叠加模型移动的根（时钟按偏移） |
| `32eb30e0c` | DECIDE 的时钟 witness 落在边界上，重放差 70 ms 没过期（token-expired.proxy） | 时钟 witness 沿移动方向再加 `ClockMargin`（60 s），公式仍可满足才采用 |
| `4b9ca100a` | CONFIRM 要求重放走过 anchor 在 target **之后**的读，致命的重放在 throw 处已经停下（token-pw-expired.mirror） | CONFIRM 对 anchor 也在 target 处截断（Composer 不变） |
| `d0502c653` | 128 个估值全部判定、只是没有机制可命名，理由却写"有估值未判定"（token-nokey） | 理由如实区分 |
| 树 `e9dff9ac7f1` | 工作负载没把 DataNode 的 RPC server 登记为该节点，visible-gs 的 target 落在 `workload/unregistered` | `CausynthCluster` 登记 `datanode.ipcServer` |

## 7. 限制

* **具体值检查只能靠故障改变控制流来触发**。GS、blockId、seqno、offset、租约持有者的源头
  是计数器和字符串，不是根；单次运行里它们总是具体值。261 个故障重放没有一次让检查判错：
  传输故障让到达检查的路断掉（ABORT）或被重试、流水线恢复吸收。
* **语义应答永不注入**。close-retries 要失败，需要 NN 的 `complete()` 一再正常返回 false；
  这必须来自因果链（例如 DataNode 的块报告迟到），当前的根里没有能导致它的。
* **循环里的门让义务数翻倍**。ack-seqno / pipeline-reply 的检查在 `ResponseProcessor` 的逐包循环里，
  每个包的 IPC/DataTransfer 门各是一个故障候选，嵌套世界又在其上翻倍：第 0–3 波 43 → 88 → 620 → 1080
  个义务。三个 flush case 在第 3–4 波被我停掉（它们挤占了全部 20 个槽位）；已跑的约 1700 个 session 里
  检查到达 4000 余次，致命臂 0 次。循环体里同址的门需要按"第一次/非第一次"合并，是下一步的约束。
* **flush 工作负载在全序重放下时序敏感**。3 个 case 的种子重放卡住：录制事件在重放里
  迟迟不出现，每次空等 16 秒后放弃，累计超过客户端 495 秒的 ack 超时，或者流水线建立
  失败、唯一的 DataNode 被排除。这是调度强制器已知的一类问题（等一个不会来的事件）。
* **嵌套世界里的根**。只在父故障世界里出现的门（重试产生的 RPC）在种子录制里没有 mint，
  嵌套义务无法聚焦植入（`ASSIGNMENT_UNMINTABLE`），探索深度因此受限。
* **估值上限 128**。token-nokey 的组合达到上限。
* **wire 流仍是 block-key 族手写的**（§8）。
* **多 DataNode 的客户端流水线不可用**：NameNode 用 `ThreadLocalRandom` 选流水线头，
  重放无法复现，所以 flush/softlimit 都只用一个 DataNode。

## 9. 已有的集群单测当工作负载（g0–g2）

**做法**。工作负载清单（`~/gc-out/workload-inventory/`）跑了 301 个 MiniDFSCluster 单测：每个 ad-hoc 检查都被几十个
测试覆盖（覆盖率含集群启动，不等于窗口内到达）。树里的 `CausynthCluster#AUTOMATIC`（`fdf425b3e9c`）让任意集群测试
不改一行就成为工作负载：它建的 MiniDFSCluster 自己注册（`auto0/nn<i>`、`dn<i>`、`client0`）并打开录制窗口；case 名
`<check>.<TestClass>-<method>`（`789144da7`）。挑了单 DataNode、跑得通的 7 个测试 × 相关检查共 20 对：

* **g0（发现）**：18/20 对在录制窗口内真的到达检查点，占用写进 `occurrences.tsv`（`8d9af33a8`）；
  complete-uncommitted/TestLeaseRecovery、visible-gs/TestTransferRbw 只在建集群时到达，剔除。
* **g1（18 个 campaign）**：11 个的种子重放没有复现到检查点（MISSING），7 个走完全程；**致命臂 0 次**。
* **g2（修复后重跑 2 个）**：种子重放从 31/93、31/94 个调度槽涨到 89/93、88/94，都走完全程；致命臂 0 次。

| case | 轮 | 种子重放 槽 | 义务 接纳/拒绝/UNSAT | 结论 |
|---|---|---|---|---|
| lease-missing.TestLeaseRecovery-testLeaseRecoveryAndAppend | g1 | 87/94 | 65/29/17 | 59 条路径全部自相矛盾（见下），组合被扣下 |
| reader-chunk.TestFileConcurrentReader-testUnfinishedBlockRead | g1 | 109/112 | 103/149/35 | 路径都是健康臂上的具体判定 |
| commit-gs.TestLeaseRecovery-testLeaseRecoveryAndAppend | g2 | 89/93 | 22/3/4 | 同上；另有 22 条 FRAME_UNBALANCED（已修，`e13c75bb9`） |
| lease-holder.TestLeaseRecovery-testLeaseRecoveryAndAppend | g2 | 88/94 | 5/0/0 | 同上 |
| finalize-gs / sender-gs / recv-offset（4 个） | g1 | 41–252 | ≤1 | 同上 |
| token-* 5 个（HA 故障切换）、visible-gs 2 个、commit-gs/lease-holder 首跑 | g1 | 30–131 | — | 种子重放没复现到检查点 |

**重放为什么复现不了，修了什么**（逐个对比 `recorded_schedule.jsonl` 与重放会话的 `schedule.jsonl` 找第一处分歧）：

1. **推迟的 RPC 响应**。NameNode 的名字空间写操作把响应推迟给 FSEditLogAsync 的同步线程：处理线程和同步线程谁后完成
   谁发送。录制（JIT）和重放（解释器）判得不一样，响应的 SEND 挂在不同上下文、生产者端点也不同，客户端之后的锚点
   全部改名，调度前缀每次空等 16 秒。修法（`784bebc9e`）：响应的端点和调度站位在**收到请求时**就定下，谁发都一样。
2. **HA 客户端随机选 NameNode**。`dfs.client.failover.random.order` 默认为真：录制先连 nn2、重放先连 nn1。
   `CausynthCluster.configure` 把它设为假（`3d4f4066cfa`）。
3. **排队区域留下已认领任务的帧**。BlockManager 的 `processQueue` 是区域根又自己排空队列，最后一个任务的启动层留到
   区域关闭之后（FRAME_UNBALANCED，BLOCKING）。区域退出时关闭它内部认领的工作（`e13c75bb9`）。

**这些新协调上的假阳性过滤（真实运行，不构造）**：

* **探索阶段：模型可行、执行实现不了 → 不采纳**。reader-chunk 的 149 个、lease-missing 的 29 个义务被执行否决。
  典型的一条：求解器要在客户端 RPC 的发送门（`Client$Connection.sendRpcRequest`）和响应门（`getRpcResponse`）上
  同时注入故障，但在第一处故障的世界里，客户端再也没走到第二个门，重放没有 mint 这个根——"this replay published
  no root mint row for [...], so its session states nothing about the value it ran the root(s) the obligation moves at"。
  模型里的"故障组合"在真实执行里不存在，这条路径不进入语料，也就不会被当成见证。
* **组合阶段：公式在任何世界都为假 → 扣下，不发布任何结论**。lease-missing（`FSNamesystem.recoverLeaseInternal`
  的 "lease == null"）59 条组合路径的致命项都要求 lease 引用为 null，而录制里它是一个确定的非空对象身份
  （unsat core 只有 `identity != nullRef`、`path_fatal`、选中路径三条）。这种路径既证明不了 bug，也不能拿来
  "反驳" bug；composer 以 PATH_SELF_CONTRADICTORY 把整次组合扣下，而不是报 UNSAT。
* **判定阶段：具体健康臂**。commit-gs、lease-holder、reader-chunk 等的锚点在健康臂上做的是具体判定（比较的是字符串、
  引用、计数器，不是根），所有到达锚点的路径被拒（ADMISSION_GAP），不发布候选。

**没有找到新 bug**。原因两条，都指向下一步：
(a) 这些检查比较的值（租约持有者字符串、lease 引用、块的 GS、key 映射）在单次运行里是具体的——F2 目前只能跟踪
VM 能版本化的 int/long 字段，容器、引用、字符串要在 VM 里加一个"从第一次具体写入开始观察"的入口（容器日志的
INITIAL 版本已经有了）；(b) 多个 HA/时序敏感的测试还需要按上面的方法逐个找重放分歧。修复后的 18 个 case 正在重跑（g3）。

## 10. 共享状态真正被跟踪之后（2026-09-26 晚，g3/g4/f2/f3）

**五个根因，都是通用修复**：

1. **STATE 族一直是 0 的原因在 VM 里**（`578bd7e2f`）。SYMBOL-SCOPE F2 在每个被跟踪字段的写点前织入
   `observeExactPrimitiveField`，但这个 VM 入口只设了字段的影子值，没有开版本日志；而一次具体值的 `putfield`
   只在日志已经存在时才记版本（`bytecodeInterpreter.cpp` 的 carrier 规则）。结果是：自 `74ffdb60e` 起，**没有一次
   被观察的具体写留下过版本**，读也就没有可连接的写者。现在观察即开日志（INITIAL = 窗口前的值，读到它就钉在它上），
   随后的写成为 WRITE、之后的 getfield 走版本日志。新 smoke `RegionObservedConcreteWriteSmoke` 在旧镜像上失败
   （`selected:false`），新镜像上与其余 smoke 一起通过。新镜像单独放在 `~/gc-out/vm-f2/j2sdk-image`，没动正在跑的共享镜像。
2. **17899-bug3 的 OOM**（`c30edc3eb`）。"一个读是否决定分支"的回溯穿过了 wire 边：`DataEncryptionKey.keyId`
   只是被拼进 SASL 用户名，由接收方判定，却被当成本地的跟踪读；DIGEST-MD5 由它派生会话密钥，fault 世界里 CBC
   加密的表达式到了 33 MB。现在回溯停在 wire 边（接收方在它的 attach 上判定，F3）。v63 里 bug3 恢复 PASS。
3. **HA 集群测试的响应身份**（`31d364532`）。NameNode 的处理线程在请求到来之前就进了一个长期的 `doAs` region
   （上下文 Lost，索引数的是这个处理线程接过的调用），`7e18f61df` 用"收到请求时的当前 occurrence"作响应端点，
   于是每个处理线程的第一个响应共用一个端点，客户端第 k 个回执对错了调用（种子重放在第 57 槽分叉）。现在响应端点
   取请求自己的作用域（它的 anchor），与哪个处理线程接手无关。

4. **引用字段里写入的 null 没有写记录**（`88f18feb6`）。F2 生效后，被跟踪的 int 读使更多分支变成符号的，
   受守卫的具体写开始给引用字段记版本；写入 `null` 时版本表达式是 VM 的 null 符号，不带类名，RowRuntime
   不发布这条 WriteRow，读它的路径被整条拒掉——v64 里 17960 的 ordered=false 见证路径就这样丢了（一个世界里
   24 个这样的版本，都是快照 diff 链上被清空的 `posteriorDiff`）。null 本来就是引用，按引用发布。
5. **接口调用只解析到"自己实现了接口"的类**（`653128e23`）。`Replica.getGenerationStamp()` 实际执行的是
   `Block` 的方法（`ReplicaInfo extends Block implements Replica`），`Block` 自己不实现 `Replica`，于是 DataNode
   上所有读副本 GS 的检查（visible-gs、sender-gs）在静态切片里根本到不了这个字段，它的写者也就不会被规划。
   现在按 CHA 解析：每个具体子类型的方法查找结果都是目标，反向也经过继承该方法体的每个子类型。离线重跑
   visible-gs 的静态阶段：副本 GS 的读接上了 `Block.generationStamp`，切片只大了 13%（16423 → 18499 条边）。

**新 VM 上的集群测试（f2，p79 + vm-f2）**，与旧 VM 的 g3 对比：

| case | g3（旧 VM） | f2（新 VM） |
|---|---|---|
| commit-gs.TestLeaseRecovery | 6 个 session、23 条写记录、0 条被接纳路径，ADMISSION_GAP（锚点是具体健康臂） | 10 个 session、205 条写、3 条路径，锚点变成符号（`commitBlock` 的 GS 比较读的是被跟踪的 `BlockInfo.generationStamp`），**PATH_SELF_CONTRADICTORY** |
| reader-chunk.TestFileConcurrentReader | 5 个 session、51 条写、0 条路径 | 43 个 session、639 条写、1 条路径，PATH_SELF_CONTRADICTORY |
| lease-missing.TestLeaseRecovery | PATH_SELF_CONTRADICTORY（59 条） | 同，10 条路径 |

**新的真实过滤例子（f2，commit-gs.TestLeaseRecovery）**：`BlockManager.commitBlock` 比较 NameNode 存的块 GS 与
客户端上报的 GS。旧 VM 上这个读是具体值，路径直接被当作"健康臂上的具体判定"丢掉；新 VM 上它是一个跟踪读，
读到的是 `addBlock` 那次调用写的版本（v109），而同一位置的另一次写（v198）是读者自己 occurrence 里的
`setGenerationStamp`，不是备选写者。只有一个写者，读被钉在它写的值上，于是"GS 不一致"在任何世界里都不可满足，
composer 以 PATH_SELF_CONTRADICTORY 扣下整次组合——模型在这个工作负载里找不到任何能让检查触发的写者顺序。

**还没解决的两件事**（SYMBOL-SCOPE §4、§6 已写入）：
* **写者索引**。一次存储只在运行中的任务里被观察；一个还没有任务写过的位置被读时，不产生 ReadRow，闭包不向任何
  写者要求，写者也就永远不成为任务。visible-gs.TestFileConcurrentReader 里 DataXceiver 写副本的 GS、IPC 处理线程
  读它，两边都没接上（种子里被跟踪的只有请求自己转换出来的 `ExtendedBlock`）。§3.1 的做法是在录制时按具体对象
  挂候选读写点、建 `Writers_W(l)`，PLAN 把目标相关 occurrence 所读位置的写者都变成任务。
* **HB 判定的过近似**。`Arms#concurrent` 把同一个客户端线程先后引起的两个 NameNode occurrence（addBlock、complete）
  视为并发：客户端等待第一个响应这件事不在任何一行里。因此一个读可能被给到"更早调用的写"作备选，而程序顺序不允许。
  这正是 CONFIRM 偏序关卡要拦的一类：模型要求的 reads-from 在重放里排不出来。

**HA 与流水线恢复测试的重放**：f3（p80，响应身份修复后）6 个 HA token case 仍然 MISSING。第一处分歧换了位置：
DataNode 三个 BPServiceActor 的第一个窗口内请求，录制里三个 NameNode 都把块操作入队（`BlockReportProcessingThread.enqueue`），
重放里同一请求身份下没有入队——请求的内容不同，身份相同（心跳是否到期由真实时钟决定）。visible-gs.TestClientProtocolForPipelineRecovery
是同一类。这需要调度层面的时钟处理，尚未动手。

## 8. 下一步

**符号的范围从致命切片推出**（老板 2026-09-26 的方向，设计 [`SYMBOL-SCOPE.md`](../design/SYMBOL-SCOPE.md)）。
本报告的结果说明了为什么需要它：这批检查的比较对象（GS、seqno、offset、key 的字段）在单次运行里都是具体值，
因为只有声明的根是符号；共享字段没有版本，STATE 族一次都没出现，CONFIRM 的偏序关卡也就没被真实地用到。
已经做了的：
1. 切片既读又写的基本类型实例字段都被跟踪：每个写点被观察（`putfield` 也算），读它的 region 从入口记录分支
   （`74ffdb60e`、`6715319f3`）。
2. 作用域在切片停下的地方自动生长到不动点：callee 的类、字段的 owner 与写者、setter 的调用者；目标 region
   的根是后置条件，谁移动了根谁被撤回（`0c0788e32`、`dbab95a77`）。
3. 已有的集群单元测试不改一行就能当工作负载（树里 `CausynthCluster#AUTOMATIC`，`789144da7`），
   工作负载清单 301 个测试，每个 ad-hoc 检查都多出几十个可达的测试。
还没做的：wire 流的自动配对（下面的设计）。

**传播边界的自动化（wire 流）**。设计（尚未实现）：

1. **候选**：Soot 扫描作用域内的调用：生产端 `M$Builder.setF(T)` 的实参，消费端
   `M.getF()` 的返回值，`M` 是 protobuf 生成的消息类，`T` 是 VM 能承载的基本类型；
   按 `(M, F)` 配对，一个字段一条 WIRE_FLOW，不再手写。
2. **方向与传输**：只有 Hadoop IPC 有信封。`*Service$BlockingInterface` 的方法参数类型是
   顶层请求消息、返回类型是顶层响应消息；沿 `Builder.setX(子消息)` / `addX(子消息)` 求包含
   闭包，嵌套消息继承顶层消息的方向。DataTransfer 的 op 消息（`OpWriteBlockProto` 等，走
   `Sender`/`Receiver`）和 fsimage 的消息不属于任何 RPC 接口，自然被排除——它们要各自的载体。
3. **frame**：同一消息里同形的多组叶子（`ExportedBlockKeys` 的 `currentKey` 与 `allKeys[i]`）
   靠 frame 方法分开；自动规则取"构造该嵌套消息 builder 的方法的调用者中，在循环里调用它的
   那个"，否则以 RPC 消息本身为 frame（按序数配对，要求编码与解码的顺序一致，这一点要在
   SEED 用录制校验）。
4. **只在生产端导出**：修掉"响应端口在接收节点也导出"的老问题
   （11741 调试时发现：8700 个 attach 配到了接收侧没有表达式的本地端点），方向决定哪一侧导出。

它对这批 adhoc 检查的帮助有限：GS、seqno、offset 的源头不是根；token 的过期时间在
`BlockTokenIdentifier` 的字节序列里（`TokenProto.identifier` 是 bytes），不是 protobuf 字段。
它的价值在于让 block-key 族以外的 case 不必手写映射。
