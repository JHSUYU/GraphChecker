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
| 假阳性过滤（全部来自真实运行） | §5：公式在录制取值下可满足 ×6（sender-gs、token-expired、commit-gs、lease-holder）；探索中模型可行、执行否决 68 次（两个故障不独立、门没经过、根只存在于故障世界）；**跨运行拼接的消息配对**（token-nokey.mirror / .replicate：只有把一次运行的状态配上另一次运行 NN 下发的 key 列表才会失败，每次运行自己的配对下 UNSAT，DECIDE 不命名机制、不发布）；**共享字段的 HB 过近似**（commit-gs.TestFileAppend2-testSimpleAppend：STATE family 让目标处的 GS 读看到更早一次 RPC 的写，DECIDE 给出 STATE_PAIRING_FLIPPED；CONFIRM 按模型的偏序重放，程序排不出这个顺序——调度空转 109 秒、649 个槽放弃，运行走了模型没选的 ORDER——判为 SAT_UNCONFIRMED 扣下，§11）；§13.6：commit-gs.TestClientProtocolForPipelineRecovery（STATE family 让 commit 处的 GS 读配上 pipeline recovery 写的 1002，录制取值下就 SAT，被自检扣下）；token-nokey.replicate（同一 world 的两次重放把一个 consumer 配给不同生产者，MARKER_FLIPPED 被 TOPOLOGY_DIVERGENCE 扣下） |
| 集群单测当工作负载 | 301 个测试的清单；20 对（检查 × 测试）里 18 对在窗口内到达检查；18 个 campaign 首跑 11 个种子重放复现失败，逐个找出 3 类分歧并修掉（推迟的 RPC 响应、HA 随机选 NN、排队区域的帧），修后种子重放 88–89/94；致命臂 0 次，新 bug 0 个；过滤实例：执行否决 178 个模型、59 条自相矛盾路径被扣下（§9） |
| 九个 case | 最终运行（2026-09-28，§13）：九个 case 一个一个独占十台 lift，**9/9 PASS**（exit 0、FINAL_READY、无 BLOCKING、CONFIRM true），用时 481–1378 s（v88 共享池子时 667–3275 s）；闭包 2–13 个 region；七个 case 的 .smt 签名与 v88 相同，11741 CLOCK_SKEW（NN 与 DN 时钟），17899-bug2 MARKER_FLIPPED（IPC 响应故障）；这两个在声明的 (r,c,i) 第一次出现 fatal 时停止探索（§13.5） |
| 不动点与故障对图的改变 | §13.3–13.5：17897 四波到不动点（31 → 68 → 8 → 0 个义务，两次故障 GROW 暴露 client 换 DN 与 dn0 的 peerSend）；九个 case 的逐波图变化与 graphdiff 故障模式（响应丢失 → 状态分叉 → ESCALATION，请求丢失 → 重试恢复）；搜索空间为什么有界、规划器与 COMPOSE 的平方项；图页 https://claude.ai/artifact/7JaJAryJgqiqyFx3ub31TK |
| ad-hoc 全量（a10） | 52 个 ad-hoc case 全量重跑（a10，被重启打断的与工具状态挡住的在 a10c 重跑）：**没有新 bug**；被接受的只有 2 个 CLOCK_SKEW（时钟同步的设计前提）；其余按原因归类：诚实否定 17、未陈述的读 10、φ 为具体值 9、种子重放时序未到达 6 …（§13.6） |
| 修掉的引擎缺陷 | §6 的 15 个 + §12 的 6 个 + §13 的 6 个（规划器行索引、工具自身状态不发行、slot 先等空间再认领、root 表只建一次、COMPOSE 并行求解、stop-at-fatal 与见证后的截断不扣见证），另有 1 处工作负载登记修复 |

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

* **跨线程的共享字段边第一次在集群测试里出现**（f4，p81 = CHA + 新 VM）。visible-gs.TestFileConcurrentReader 的
  种子会话里，IPC 处理线程在 `getReplicaVisibleLength` 读副本的 `generationStamp`（`INSTANCE/58#40`，版本 158），
  这个版本正是 DataXceiver occurrence（`Root:DATA_XCEIVER`）写入副本时留下的；种子计划也第一次包含了 DataXceiver
  里写 GS 的 `Block.set`/`setNumBytes`。这就是 §3.1 的 Writers_W(l) 边：读者和写者在不同线程、不同因果上下文。
  这条路径最后仍被拒，原因是下一条。
* **与检查无关的分支拖垮整条路径**。sender-gs.TestClientProtocolForPipelineRecovery（f4）：块 id 是符号的，拼进
  块文件路径（`java.io.File.path`），路径上对文件名做 `substring` 等字符串运算的分支都进了路径条件；composer 只会
  降阶 `concat/length/equals/contains/startsWith/endsWith/isEmpty/toString`，这条路径因此被拒。这些合取项与检查
  比较的 GS 不共享变量，录制值本来就满足它们。已按约束独立性（KLEE 的做法）改 composer（48b12e755）：只保留与
  致命项、某个 arm 送来的值或会话根共享变量（符号名，或被跟踪的存储位置）的合取项和读，传递闭包；其余合取项不进
  公式，它们的变量保持录制值。
* **目标 occurrence 的声明依赖 region id**。CHA 修复让 visible-gs、recv-offset 的目标 region 根外移一层，
  `occurrences.tsv` 里的声明随之失效（DECLARED_TARGET_OCCURRENCE_UNOBSERVED，已重新发现并更新）。region id
  由静态分析决定，分析每变一次就可能要重声明；声明写成"节点上第 k 个到达被注解目标的 occurrence"会更稳，
  需要 DECIDE/CONFIRM 解析声明的地方一起改。九个 case 这次没有受影响。

**HA 与流水线恢复测试的重放**：f3（p80，响应身份修复后）6 个 HA token case 仍然 MISSING。第一处分歧换了位置：
DataNode 三个 BPServiceActor 的第一个窗口内请求，录制里三个 NameNode 都把块操作入队（`BlockReportProcessingThread.enqueue`），
重放里同一请求身份下没有入队——请求的内容不同，身份相同（心跳是否到期由真实时钟决定）。visible-gs.TestClientProtocolForPipelineRecovery
是同一类。这需要调度层面的时钟处理，尚未动手。

## 11. 共享字段假阳性：HB 过近似的见证被 CONFIRM 扣下（2026-09-27，v69–v77）

**检查**：commit-gs（`BlockManager.commitBlock` 的 "Commit block with mismatching GS"），在
`FSNamesystem.commitOrCompleteLastBlock` 上。工作负载 `TestFileAppend2.testSimpleAppend`；目标是这个 region
的第三个 occurrence：第二次 append 之后，客户端的 `getAdditionalBlock` 提交上一个块。

**录制里发生了什么**（seed 的写日志）：

| 写者 | 线程 / occurrence | 写入的 GS |
|---|---|---|
| 第一次 `getAdditionalBlock` 分配块 | NN IPC 处理线程，region occurrence | 1001 |
| 第一次 `completeFile` | NN IPC 处理线程，region occurrence | 1001 |
| `updatePipeline`（两次 append 各一次） | NN IPC 处理线程，**不在任何 region 里** | 1002、1003 |

目标处 NN 读到的 GS 是 1003，客户端上报的也是 1003，相等，健康。

**组合出的公式**（`accept-v75`/`v76`，一条路径）：目标处的 GS 读是一个 STATE family，三选一

```
writer_arm A  : GS = 1001   (getAdditionalBlock#1 的写)
writer_arm B  : GS = 1001   (completeFile#1 的写)
observed_arm  : GS = 1003   (录制本身：updatePipeline 的写，没有 region 归属)
phi           : GS ≠ 1003   (客户端上报 1003)
```

DECIDE：**SAT_CANDIDATE，STATE_PAIRING_FLIPPED**，在录制的赋值（valuation 0，没有移动任何根）上成立：
见证让目标处的读"看到"第一次分配或第一次 complete 写下的 1001。

**为什么这是假阳性**：客户端的 RPC 是同步的，每次调用都等上一次的响应回来才发下一次。第三次
`getAdditionalBlock` 发出之前，`completeFile#1` 和两次 `updatePipeline` 都已经返回，它们对 GS 的写都
happens-before 这次读，读不可能看到 1001。GraphChecker 的 `Arms.concurrent` 只沿 anchor 链判断先后：
读者的链是 NN 处理器 ← 客户端 occurrence ← 上一次响应的 NN **角色** scope ← …，一路到客户端的根；但
这条链经过的是那几次 RPC 的**角色** occurrence，而写者是这些 RPC 里的 **region** occurrence，
`ancestor()` 认不出它们，于是判为"并发"。这正是 SYMBOL-SCOPE 里预料的 HB 过近似。

**过滤发生在 CONFIRM**：CONFIRM 用被选中会话（seed）的世界重放，要求模型选中的每条边都被走到、目标处
走到致命分支。

* v75、v76：`confirmed=false`，"the run published no target row that reached the anchor and observed the
  fatal"。重放中目标处读到的仍是 1003，没有不一致，**声明降为 SAT_UNCONFIRMED，候选被扣下**。
* 这两次 CONFIRM 只要求了 ANCHOR 一条边：模型选定的写者没有变成 STATE 边（下面第 7、8 条修复）。
  v77 里 CONFIRM 额外要求"目标处的读读写者 A 的版本"（版本 57，第一次 `getAdditionalBlock` 写的
  1001），并要求这次读先于 A 之后的写者（3 条 ORDER）。**这个偏序在程序里排不出来**：调度器按它把
  `completeFile#1` 挡在目标之后，而客户端要等 `completeFile#1` 返回才会发出目标 RPC。重放日志：
  从第 53 个槽起 520 个槽一直在等客户端 `DFSOutputStream.completeFile` 的 WAKE，运行空转 109 秒；831 个
  槽里 73 个按序执行，649 个在 2 次停滞中放弃，程序按真实顺序跑完。结论 `confirmed=false`：
  "the run took an edge the model did not choose: ORDER …commitOrCompleteLastBlock → commitBlock…"，
  **SAT_UNCONFIRMED**。这就是"共享字段的偏序不可满足，CONFIRM 停在它上面"的真实例子。

证据：`~/gc-out/evidence/fp-commit-gs-state-v75/`、`fp-commit-gs-state-v77/`（claim、manifest、公式、
CONFIRM 的期望边与结论、v77 的调度停滞日志 `schedule-stalls.txt`）。

**为了让这个 family 出现并被检验，沿途修掉的通用缺陷**（每条都是全局修复，九个 case 同步验证）：

1. `97add9da3` 普通 RPC 没有声明端口，客户端的发送端点从不进入语料：NN 处理器的 anchor 链一律追不到根，
   `Arms.concurrent` 全判"不并发"，NN 状态上一个 STATE family 都没有。activation 现在带上它 anchor 的发送端点。
2. `50c844ea6` 链接着断在 NN 的角色 scope：角色 occurrence 没有 activation 行。发送消息的角色 scope 现在发布
   一条 ambient activation（带它自己的 anchor 生产者）。探针：GS 读的备选写者 1 → 3。
3. `aa0a18520` `guardedReadTerm` 把被跟踪的读内联成观察到的写值，致命谓词和分支条件都落在常量上，family
   选哪个写者都动不了它。标量读现在降阶为读行的符号，由状态 join 或 family 绑定。
4. `22f2707a1`（VM）区域外线程（`updatePipeline` 所在的 IPC 线程没有 concolic 上下文）对被跟踪位置的写不记
   版本，读解析到过期版本，路径自相矛盾（`compare(1001,1002)==0`）。现在记一个无归属的具体值版本。
   smoke `RegionUnattributedWriterSmoke`。
5. `9dc50f730` runtime 把无归属版本当作畸形信封，整个位置（GS、numBytes）连同所有读一起丢掉；现在"写者
   全有或全无"都合法，只有一半才算畸形。
6. `2671615d8` + `39a188443` 这种读没有写行可 join：读行现在陈述那次区域外写留下的常量；family 增加一个
   "观察臂"（录制本身），与各写者多选一。
7. `cdf205653` CONFIRM 的 `stateEdges` 跳过录制版本没有写行的读，模型为它选的写者从不被检验。
8. `e542e1198` 写者臂的 `groupId` 是写者 occurrence，CONFIRM 却拿它去查写**端点**：真实组合里模型选定的写者
   从来没有被 CONFIRM 检验过（单元测试恰好用端点 id，所以没暴露）。现在按臂填充的 STATE interaction 匹配。
9. `dfa9afdf1` 兜底读名 `<loc>@v<n>` 只在单个 session 内有意义，两个分叉的重放在同一个名字上给出 J 和 Z
   两种 sort（17897 v67 四个阻塞 gap）。名字现在带上 session。

同一时间段修掉、由这次扩大的跟踪面暴露出来的其它通用问题：`1a8ffa4ce`（VM 把 JCE/JCA 的摘要、MAC、
密码实现当作具体子树；11741 的 Balancer 把符号 keyId 送进 DIGEST-MD5 后，seed 表达式到 41 MB）、`4590f3e38`
（VM：符号下标读只是"命名"了数组，之后按具体下标扫描读堆里的值；17960 的 FSImage 保存在 30 秒内涨到
16 GB 被杀）、`a4c1778f7`（时限内被 SIGKILL 不再误报成超时）、`1c32d953e`（诊断 gap 有界；11741 规划器
OOM、2.5 GB gap 文件让 jq 截断）、`39b2e37d6`（IMPORT 闸门逐会话读取，11741 的 240 个会话从 8 GB OOM
降到 473 MB）。

## 12. 不动点探索 + 闭包 GROW 的引擎上重跑（2026-09-27，a8–a9f）

引擎：obligation 按守卫依赖去重、探索跑到不动点、闭包驱动 GROW（`c49e42aa9` 到 `bf164f035`）。52 个 ad-hoc case
按批次跑在 p99→p106 上；每一轮暴露的缺陷都按通用方式修掉后再重跑。

| 轮次 | 快照 | case | 结果 |
|---|---|---|---|
| a8 / a8r | p99 `003b0261a` / p101 `efa7637d9` | 34 + 6 | INCONCLUSIVE 24，MISSING 13，**SAT_UNCONFIRMED 1**（commit-gs.TestFileAppend2，§11 的共享字段假阳性在新引擎上复现） |
| a9 | p102 `032bb0fd7` | 24 | MISSING 19（13 个是本人 `37c9a4381` 的回归，见下 3），INCONCLUSIVE 5 |
| a9b | p103 `d808d2982` | 19 | MISSING 17（readVLong 被循环预算截断，见下 3） |
| a9c | p104 `13ddabb62` | 17 | **SAT_CANDIDATE 2**（CLOCK_SKEW，CONFIRM=true，被 OCCURRENCE_ADDRESS_SHARED 扣下，见下 5），INCONCLUSIVE 6 |
| a9d | p105 `df0f73d24` | 20 | INCONCLUSIVE 9；token 的 selector 因折叠规则改变而过期 |
| a9e | p106 `ab01c9576` | 8 | **PASS 2**：token-expired / token-pw-expired × TestFailoverWithBlockTokensEnabled |
| a9f | p106 + 树 `cea6fb0bf6c` | 6 | 等待修复后 6 个种子重放全部到达 target（此前全是 MISSING）；INCONCLUSIVE 6：token-expired.mirror NO_SUPPORTED_WITNESS（见下）、token-nokey.mirror PATH_SELF_CONTRADICTORY + 闭包在 64 个 task 处截断（BOUND 陈述）、token-nokey.replicate 34 个 TOPOLOGY_DIVERGENCE、blockid/pw-expired.mirror 种子重放分歧（见下）、password.mirror φ 为具体值；4 次故障 GROW |

**被接受的发现（PASS）**：`adhoc-token-expired.TestFailoverWithBlockTokensEnabled-ensureInvalidBlockTokensAreRejected`
与 `adhoc-token-pw-expired.…` —— CLOCK_SKEW，polarityDecides，移动的根是 DataNode 在 writeBlock occurrence
（`REGION.f5aa492d`，`Root:DATA_XCEIVER#1`）里读到的时钟；CONFIRM：`confirmed=true … every edge the model chose was
taken, and the anchor observed the fatal`。与 §5.4 的 mirror/proxy 是同一类：HDFS 假定各节点时钟大致同步，DataNode
时钟比 NameNode 快出一个 token 寿命，块 token 就被判过期。它来自一个**现成的集群单测**（没改一行），不是专门写的工作负载。

**这些轮次暴露并修掉的引擎缺陷**（都在 main，均为通用修复，九个 case 用 v85 回归）：

1. `032bb0fd7` 表达式是 DAG，却被当成树序列化：`File.getParent` 链 94 层、389066 个节点里只有 198 个不同，ref 的摘要和
   `expressions.json` 都按树展开（239 MB、重写永远写不完，finalize-gs / recv-offset 的种子重放卡死）。现在会话表用已有的
   Merkle 编码（CONTRACT-SPEC 本来就这样规定），ref 是 Merkle 锚点的前 16 位：239 MB → 0.6 MB，finalize-gs 852 s 跑完。
2. `6d9a4b4fe` 调度器的自等待：一个 occurrence 的线程等在自己已经越过的槽前面（NN 处理 DN 块报告的线程这次没有 enqueue，
   却在 SEND 响应前等自己录制里的 enqueue），只有 watchdog 超时（16–49 s）能解开，排在后面的 addBlock 超过客户端 60 s IPC
   超时（a8 reader-chunk.flush、sender-gs.flush、a8r addblock）。现在等待者立即放弃自己 (context, occurrence) 在前面没做的槽。
3. `13ddabb62` 循环预算按**整个 region 激活**累计：target 的 occurrence 变成整条 DataXceiver 连接后，readVLong 被多次调用，
   累计第 9 次就截断，永远走不到 checkAccess。两种预算（展开界、fixed-count 体上限）现在都按 (循环, 方法激活的 frame token)
   计数，open/close invocation 钩子整个删掉。途中本人 `37c9a4381`（假定数组长度在循环前计算）是回归：javac 在下标循环的
   header 里重读 `arr.length`，13 个 case 在 INSTRUMENT 被拒；已由 `29a65ce30` → `13ddabb62` 取代。
4. `3438b585a` String 语义：VM 本来就把 String 调用记成 `OpStrExpression`，缺的是降阶。HDFS 把块 id 和 GS 写进文件名
   （`blk_<id>_<gs>.meta`）再读回来，a8 的 finalize-gs / ack-seqno / sender-gs 因 `substring`、`charAt`、long/char 的
   `toString` 拒绝而整条路径丢弃。现在它们按 Java 语义降阶（越界即未定义）；z3 没有 last index，`lastIndexOf` 用一个无量词公理
   唯一确定。a9d 里这些 case 不再有 MODEL_SEMANTICS_MISSING，停在下一个原因（未陈述的 map 读）。
5. `df0f73d24` **老板对折叠规则的修正**（"Lost 不折叠"）：DataXceiver.run 是静态回溯走到线程入口得到的 TASK_ENTRY region，
   它在连接的第一条消息之前打开，acceptor 不给 start frame，context 是 Lost，于是一个 DataNode 的所有连接共享一个地址。
   现在以 Lost 打开的 occurrence 不再折叠之后在有 context 时进入的 region，后者按 (r,c,i) 自己成为 occurrence
   （`Root:DATA_XCEIVER#k`）。a9c 两个被扣下的 CLOCK_SKEW 在 a9e 发布。
6. `7f90ff7b0` 拒绝信息：写行存在、只是它的表达式降阶失败时，不再说"没有这个版本的写"。

工作负载侧：树 `cea6fb0bf6c`——mirror / proxy / replicate 三个工作负载在录制窗口里用写死的 15–20 s 等待，违反
"窗口内等待用 `WINDOW_WAIT_MS`"的准备规则；concolic 重放比它慢，`waitFor` 先放弃、集群关闭、源端 SASL 被中断，
种子重放到不了 target（a9d/a9e 的 token-*.mirror）。

**故障注入带来的 GROW**（`tools/analysis/graphdiff.py`）：ad-hoc 这一侧共 7 次，**全部由故障世界暴露**，暴露的都是
NameNode 的 `UserGroupInformation.doAs`（REGION.084d06ab，context Lost）——客户端/DataNode 的 RPC 在故障门上失败后，
重试把请求送进一个录制里没出现过的 NN 处理 occurrence：

| 轮 | case | GROW | 暴露它的故障门 | 被捕获为 task |
|---|---|---|---|---|
| a8 | ack-seqno.flush | 2 | `IPC:RESPONSE` | 2 |
| a8 | pipeline-reply.flush | 1 | `IPC:RESPONSE:SocketTimeout` | 1 |
| a9f | token-nokey.mirror | 2 | `IPC:RESPONSE:EOF`、`IPC:REQUEST` | 2 |
| a9f | token-nokey.replicate | 1 | `IPC:RESPONSE` | 1 |
| a9f | token-password.mirror | 1 | `IPC:RESPONSE:EOF` | 0（重跑后 ADMITTED，occurrence 仍未被捕获） |

同一批故障世界里图的变化（相对各自对照重放，扣除对照噪声）：a9f 的 token-nokey.mirror 44 个故障会话里
ABORT 41、EDGE_CUT 39、STATE_DIVERGENCE 21、TOLERATE 3、RETRY 1；token-password.mirror 12 个里 ANCHOR_DROPPED 2。
其余 case 在 EXPLORE 之前就被上面的缺陷挡住，或者 target 是具体值判定；a9c/a9e 的两个 CLOCK_SKEW 直接由种子会话组合
得出（时钟根在公式里自由），没有焦点重放。九个 case（v85）里 GROW 重跑：17897 5 次、
pathA 4、pathC 4、bug1 3、pathB 2、bug3 2、17960 0。

**过滤（全部来自真实运行）**：
* CONFIRM 否决：commit-gs.TestFileAppend2（a8，SAT_UNCONFIRMED）——§11 的共享字段 HB 过近似在新引擎上复现；这几轮里没有
  出现第二个被 CONFIRM 否决的候选，所以"共享字段之外的原因"目前没有真实例子。
* 身份关卡：a9c 的两个 CLOCK_SKEW 已经 CONFIRM=true，仍因 OCCURRENCE_ADDRESS_SHARED（BLOCKING）不发布——证据指向的
  occurrence 不能被唯一命名时宁可扣下。
* DECIDE：token-expired.proxy（a9e）与 token-expired.mirror（a9f）NO_SUPPORTED_WITNESS。被选中的路径来自**种子重放**
  会话，`fatalObserved: true`：这两个工作负载把块 token 的寿命设成 1 分钟，concolic 重放从签发到检查超过了一分钟，
  token 在重放里真的过期了——致命臂由引擎自己的慢时钟触发，不是模型里的任何根。赋值为空、没有移动的根/时钟/配对，
  DECIDE 没有机制可命名，不发布。（种子重放若在时钟根上种入录制值，这一类就不会出现；列入下一步。）token-nokey.TestFailover（a9d）与
  recv-offset.mirror（a9）PATH_SELF_CONTRADICTORY。

**种子重放复现不了录制（mirror 工作负载，a9f）**：等待修好之后，token-*.mirror 的种子重放仍然到不了 mirror-dn：
head-dn → mirror-dn 的 SASL 握手在重放里断开（mirror 的 occurrence 没等到 SASL REQUEST 就关闭，head 收不到 RESPONSE，
`The stream is closed`，之后 head 上 `ReplicaNotFoundException`）。这个工作负载的前提是块 key 的轮换时机：录制里 head 与
mirror 在握手时持有同一把 key；重放里第 4 个槽的 head-dn 心跳 SEND 16 s 没出现、被放弃，心跳（也是 key 下发的通道）
随后自由运行，key 到达两个节点的先后与录制不同，加密协商失败。它是"守护进程时序"一类的种子重放分歧，不是 CONFIRM
否决；同一个工作负载在 pathA（织入范围小、重放快）里能复现。

**符号选择挡住 φ 的一个真实例子（recv-offset.flush）**：守卫 `header.getOffsetInBlock() > replicaInfo.getNumBytes()`
（`BlockReceiver.receivePacket`）。静态一侧选对了：`PacketHeader.getOffsetInBlock()` 的返回值是 ROOT_SITE（切片在这里
停下），`Block.numBytes` 是被跟踪的 READ_SITE。运行时这个决策（`receivePacket#u20`）的项是
`(1024 − numBytes) <= 0`：`offsetInBlock` 是常量 `Y_J_1024`，种子会话 roots 里没有它；`numBytes` 从第二个包起是读符号，
第一个包的副本在 region 外创建，读到的是常量。target 的锚是守卫的第一次执行（#u20#1），两个操作数都具体，φ 形不成。
按 SYMBOL-SCOPE 的约定，切片边界上的值"绑定、从不自由"：`offsetInBlock` 来自 DataTransfer 的包头
（`PacketHeaderProto.offsetInBlock`），要靠 wire 流配对绑定到发送端的表达式，而这一步（设计里的第 3 步）还没做，
DataTransfer 又不属于任何 RPC 接口（§8），于是它保持具体。它不是假阳性，是"被忽略的符号变量"的一个确切实例。

**仍然挡住 ad-hoc case 的原因**：守卫在具体值上判定（recv-offset、reader-header、token-password：φ 形不成，符号选择问题，
recv-offset 见上）；
未陈述的读（finalize-gs、visible-gs 的 map 读，sender-gs 的数组读）；K_L 不够（一次 `removeExpiredKeys` 超过 8 个 key）；
PATH_SELF_CONTRADICTORY（commit-gs 系列，按设计）。

## 13. 九个 case 的最终 .smt、用时与闭包；不动点与故障对图的改变；a10 全量重跑（2026-09-28）

**最终运行**：九个 case **一个接一个、每个独占全部十台 lift**（lift06–lift15 含 lift11，每台 10 个 slot，全池 100 个；
内存闸门按每台 MemAvailable 放行），驱动脚本 `~/gc-out/analysis/series.sh`。七个 case 是 v92（p113 `b9483fb8f`）；
11741 是 v93（p114 `970f9631f`）、17899-bug2 是 v94（p115 `21c42559d`），这两个打开了 `region_path_stop_at_fatal`
（13.5）。对照列是 v88（p109 `b49644426`）：那一轮九个 case 和 52 个 ad-hoc case 同时共用 9 台 × 4 slot 的池子。
v88 的 bug2 在 COMPOSE 中途遇上 06:38 的集群整体重启；它和 v90（p111，bug2 完整探索到 W8 不动点）的探索数据用于
13.3–13.5 的图分析。

### 13.1 九个 case：结论、用时三段、z3 求解

用时取自每个 campaign 的 `schedule/stage_metrics.tsv`（脚本 `~/gc-out/analysis/timing.py`）。**分析** = PREFLIGHT…SEED、
PLAN、INSTRUMENT、REPLAY、IMPORT；**探索** = EXPLORE（各波直到不动点或见证，含 GROW 重跑）；**最终求解** =
COMPOSE+SOLVE+DECIDE（COMPOSE 内部为每个 valuation、polarity 判定与路径族各解一次，互相独立的求解并行）；
**z3 单解** 是 z3 4.14.1 单独解最终 `final/candidate.smt2` 一次的墙钟时间。九个 case 全部 exit 0、FINAL_READY、
无 BLOCKING、polarityDecides、CONFIRM true。

| case | 结论（移动的根） | 总计 s | 分析 s | 探索 s | 最终求解 s | z3 单解 s | CONFIRM+EMIT s | v88 总计 s |
|---|---|---|---|---|---|---|---|---|
| 17960 | MARKER_FLIPPED（`SNAPSHOT_DELETION_ORDERED`=false） | **481** | 321 | 154 | 1 | 0.01 | 3 | 667 |
| 17967-pathB | MARKER_FLIPPED（IPC 故障标记 `REGION.763d087e`） | **579** | 249 | 299 | 20 | 0.33 | 7 | 899 |
| 17897 | MARKER_FLIPPED（`REGION.763d087e`） | **741** | 225 | 455 | 48 | 0.51 | 9 | 1288 |
| 17899-bug1 | MARKER_FLIPPED（`REGION.763d087e`） | **789** | 240 | 434 | 31 | 0.09 | 81 | 1337 |
| 17899-bug3 | MARKER_FLIPPED（`REGION.763d087e`） | **815** | 228 | 557 | 20 | 0.13 | 7 | 1300 |
| 17967-pathA | MARKER_FLIPPED（`REGION.763d087e`） | **958** | 231 | 569 | 27 | 0.45 | 129 | 1464 |
| 17967-pathC | MARKER_FLIPPED（`REGION.763d087e`） | **1194** | 248 | 715 | 79 | 0.11 | 145 | 1609 |
| 11741 | CLOCK_SKEW（NN 时钟 `08ab84c9`、DN 时钟 `ba3902cd`） | **1378** | 418 | 743 | 52 | 1.36 | 161 | 3275 |
| 17899-bug2 | MARKER_FLIPPED（IPC 响应故障标记 `REGION.9ffdee3d`） | **752** | 476 | 245 | 18 | 0.14 | 7 | —（v90 完整探索 > 2 h） |

* **分析段**基本不随池子变：225–476 s（SEED 95–120 s、REPLAY 66–301 s、INSTRUMENT ≈ 30 s），它是 head 上串行的
  种子录制、插桩和种子重放。
* **探索段**缩短最多：七个完整探索的 case 比 v88 少 30–46%（17897 837 → 455 s、bug3 992 → 557 s），来自独占
  100 个 slot 与规划器的行索引（`ff4db3a64`）。11741 与 bug2 在声明的 occurrence 第一次出现 fatal 时停下（13.5），
  11741 的探索 2350 → 743 s，bug2 只跑了一波（47 个义务）。
* **最终求解段**：COMPOSE 里互相独立的 z3 求解并行（`b9483fb8f`）、root 表只建一次（`f09f724e6`）之后，17897
  201 → 48 s、pathC 201 → 79 s、11741 337 → 52 s。
* **z3 解最终公式本身**很快：八个 case ≤ 0.51 s，11741 1.4 s（v88 完整探索的公式要 11 s，z3 统计里 `array-exp-ax2`
  实例化 113 万次；停在见证处的公式小得多）。

**.smt 的因果链**（`tools/analysis/chaincheck.py`，签名存于 `~/gc-out/analysis/chain-*.json`，逐个对 HDFS 代码核对）：
v92 的七个 case 与 v88 的签名逐项相同（17960 多了一个 `REGION.5cf88831` 整数根：两条路径的 numSnapshots 现在各是
自己那次 FSImageSaver occurrence 的符号），被移动的根都与 v54 相同。17960 的链正是机制本身：

```
path 0 (ordered=false): numSnapshots = 0+1+1-1-1 = 0,  φ: numSnapshots ≠ 1  → SAT
path 1 (ordered=true):  numSnapshots = 0+1+1   = 2,  φ: numSnapshots ≠ 2  → UNSAT
```

11741（v93）停在见证处，公式比 v88 小（路径 42 → 25、消息臂 730 → 245、ite 8024 → 2712），链仍然完整：allKeys 的
put / remove / has / read、NN 与 DN 两个时钟根都在，移动的根不变。17899-bug2（v94）对照上一次通过的 v58：
assoc_put 316 → 304、消息臂 383 → 371、ite 3817 → 3695，移动的根同为 IPC 响应故障标记 `REGION.9ffdee3d`；CONFIRM：
"the selected session is itself the run: it took every edge the model chose (2 arms, all its own deliveries), ran
every moved root at the model's value, and observed the fatal at the anchor"。

### 13.2 闭包包含多少 region

闭包 = 最后一波（不动点或见证）`tasks.jsonl` 里每个 task 的 focused occurrence 加 factor 成员（去重）；图 = 同一波
`graph.jsonl` 的节点（闭包之外还有只提供数据的节点）。脚本 `~/gc-out/analysis/closure_regions.py`。

| case | 最后一波 | 闭包 task | 闭包 occurrence | **闭包 region** | 图节点 | 图 region | 各节点上的闭包 region |
|---|---|---|---|---|---|---|---|
| 17960 | W2 不动点 | 3 | 3 | **2** | 51 | 6 | nn0=2 |
| 17967-pathB | W3 不动点 | 27 | 27 | **9** | 66 | 12 | mover=1 nn0=3 proxy-dn=5 spare-dn=4 target-dn=7 |
| 17897 | W3 不动点 | 35 | 35 | **12** | 85 | 15 | client=5 dn0=8 dn1=4 dn2=4 nn0=5 |
| 17899-bug1 | W3 不动点 | 32 | 32 | **13** | 73 | 16 | balancer=7 nn0=4 proxy-dn=1 spare-dn=4 target-dn=7 |
| 17899-bug3 | W3 不动点 | 20 | 20 | **8** | 100 | 12 | nn0=3 source-dn=5 target-dn=5 |
| 17967-pathA | W3 不动点 | 31 | 31 | **10** | 233 | 13 | head-dn=5 mirror-dn=5 nn0=3 source-dn=6 |
| 17967-pathC | W3 不动点 | 35 | 35 | **9** | 274 | 12 | helper-dn=1 lost-dn=4 nn0=3 target-dn=5 worker-dn=7 |
| 11741 | W2 见证 | 37 | 37 | **13** | 483 | 20 | balancer=6 dn1=5 nn0=3 |
| 17899-bug2 | W1 见证 | 62 | 70 | **10** | 218 | 14 | nn0=4 sps=4 target-dn=5 |

一个 region 可以在几个节点上各有 occurrence（同一段代码在 source-dn 和 target-dn 上各跑一次），所以最后一列按节点
计数的和大于闭包 region 数。17960 最小：saveNamespace → FSImageSaver.run（按两个存储目录激活两次）和重启时的
loadFSImage。完整探索到不动点时，11741 是 W6、46 个 task、11 个 region（v88），bug2 是 W8、63 个 task、10 个 region
（v90）：region 数和停在见证处时相同，多出来的是同一批 region 的更多 occurrence。

### 13.3 一个故障注入下迭代到不动点的完整例子（HDFS-17897，v88）

| 波 | 图 G_k（节点 / 边 / world） | 义务来源 | 判决 | 这一波前后发生的事 |
|---|---|---|---|---|
| W0 | 64 / 238 / 1 | IPC:REQUEST 8、IPC:RESPONSE 9、SASL 2、分支 12（removeExpiredKeys 7、addKeys 4、retrieveDataEncryptionKey 1） | ADMITTED 26、UNSAT 5 | seed 一个 world |
| W1 | 87 / 253 / 27 | IPC:REQUEST 18、IPC:RESPONSE 30、分支 20 | ADMITTED 40、UNSAT 21、NOT_ADMITTED 7 | **GROW ×2**（下），+23 节点 |
| W2 | 87 / 257 / 52 | 分支 8（retrieveDataEncryptionKey） | UNSAT 8 | 无 GROW；world 由继承的翻转组合 27 → 52 |
| W3 | 87 / 257 / 52 | 0 | — | **不动点**；v87 在这里还 GROW 了 nn0 心跳处理器，v88 被 tick bound 拦下（每波 6 条 DIAGNOSTIC gap） |

结论：MARKER_FLIPPED（IPC 故障标记 `REGION.763d087e` = true，polarityDecides），CONFIRM true。

W0 → W1 的 GROW，已在 replay 日志里核实：

1. 义务 `13d962c37468dcb7` 翻转 dn0 心跳 RPC（`Root:CLIENT heartbeat #1`）的 IPC:RESPONSE 门。
2. dn0 的 offerService 报 `IOException`，收不到带 KeyUpdateCommand 的响应，手里仍是 key 119992；NN 已滚到 119994。
3. client 做条带文件校验和时 `tryDatanode@0` 向 dn0 做 SASL 握手，dn0 抛
   `InvalidEncryptionKeyException: Can't re-compute encryption key for nonce, since the required block key (keyID=119994) doesn't exist. Current key: 119992`。
4. client 改试 `tryDatanode@1 → connectToDN → … → getUserNameFromEncryptionKey`（`REGION.d930c3a2`）。这个 occurrence
   录制里没有，闭包要求它 → GROW：插桩、义务在新树下重跑，ADMITTED。
5. 同一波另一个 GROW：义务 `3e6c229485e267da` 翻转 dn0 自己 DATA_XCEIVER 里 `doSaslHandshake` 的 SASL:REQUEST 门，
   dn0 经 `peerSend → checkTrustAndSend → send → getEncryptedStreams` 进入同一 region 的新 occurrence。

图页（逐波条形图、GROW 因果时序图、九个 case 的逐波热力图、闭包 region 表、三段用时）：https://claude.ai/artifact/7JaJAryJgqiqyFx3ub31TK

### 13.4 故障注入对图的改变（九个 case）

逐波数据由 `~/gc-out/analysis/wavestats.py` 从各波的 `graph.jsonl`、`obligations.jsonl`、`growth.jsonl`、
`gaps.jsonl` 读出（八个 case 取 v88，17899-bug2 取 v90）。

| case | 不动点波 | 义务合计 | 其中故障门翻转 | ADMITTED / UNSAT / NOT_ADMITTED | GROW | 最终 world | 图节点 W0 → 不动点 | 图边 W0 → 不动点 | tick bound gap |
|---|---|---|---|---|---|---|---|---|---|
| 17960 | W2 | 9 | 0 | 1 / 7 / 1 | 0 | 2 | 50 → 50 | 56 → 105 | 0 |
| 17967-pathB | W3 | 85 | 49 | 55 / 30 / 0 | 0 | 49 | 57 → 60 | 230 → 247 | 4 |
| 17897 | W3 | 107 | 67 | 66 / 34 / 7 | 2 | 52 | 64 → 87 | 238 → 257 | 6 |
| 17899-bug3 | W3 | 84 | 40 | 45 / 34 / 5 | 1 | 35 | 40 → 99 | 202 → 234 | 2 |
| 17899-bug1 | W3 | 122 | 58 | 68 / 54 / 0 | 1 | 56 | 69 → 78 | 283 → 325 | 4 |
| 17967-pathA | W3 | 89 | 55 | 54 / 26 / 9 | 2 | 44 | 62 → 234 | 242 → 302 | 4 |
| 17967-pathC | W3 | 123 | 63 | 71 / 49 / 3 | 1 | 63 | 80 → 278 | 297 → 342 | 6 |
| 11741 | W6 | 418 | 10 | 46 / 372 / 0 | 16 | 42 | 223 → 561 | 522 → 749 | 14 |
| 17899-bug2 | W8 | 800 | 748 | 613 / 45 / 142 | 7 | 493 | 134 → 751 | 270 → 594 | 0 |

读法：

* **故障门翻转占多数的 case**（七个 IPC 机制的 case）：World 数随故障组合增长，图的节点主要由 GROW 与故障 session 里
  新出现的 occurrence 带来（pathA 62 → 234、pathC 80 → 278：故障让 DataNode 之间的传输改走别的节点，新的
  DataXceiver occurrence 进图）。故障 session 大多 ADMITTED——门在聚焦前缀上可控，翻转总能落实。
* **分支翻转占多数的 case**（11741，418 个义务里 10 个故障门）：机制是时钟，不是故障；义务大多由 corpus 判 UNSAT，
  图的增长主要来自 W2 前的 16 个 GROW（balancer 调度在新 anchor 下的 occurrence）。
* **17960**：没有故障门，图的节点不变，边 56 → 105 来自翻转 session 里多出的配对。
* **tick bound**：心跳 tick 超出录制轮次的 occurrence 不再 GROW，以 DIAGNOSTIC gap 记下（11741 每波最多 14 条）。
* **NOT_ADMITTED**：bug2 的 142 个集中在 W1 之后的故障翻转——replay 在聚焦前缀上没能走到被翻转的那一臂
  （SPS 轮询在故障后的重试次数与录制不同），这些不算 world，也不进下一波。

**故障 session 对图的净改变**（`tools/analysis/graphdiff.py v88` 与 `v90`（bug2），输出在 `~/gc-out/analysis/graphdiff/`）。每个 ADMITTED
的义务 session 与种子 session 按五层比较（occurrence、WIRE 边、STATE 边、决策、消息），键里不含会话局部 id。world 里有故障
标记为 true 的是故障 session，其余（时钟、序号、配置 world）是对照 session，对照的差异就是重放噪声，下表是扣掉噪声后的
净模式（一个 session 可以有多个模式）：

| case | 故障 session | EDGE_CUT | RETRY | FALLBACK | RECOVERY | STATE_DIVERGENCE | ESCALATION | ABORT | ANCHOR_DROPPED | DAEMON_INFLATION | TOLERATE | 对照 session（其中 TOLERATE） |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 17960 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 1（0） |
| 17967-pathB | 44 | 44 | 27 | 0 | 8 | 34 | 25 | 1 | 16 | 0 | 4 | 11（11） |
| 17897 | 55 | 55 | 18 | 13 | 14 | 36 | 11 | 19 | 12 | 0 | 1 | 11（11） |
| 17899-bug3 | 34 | 34 | 11 | 0 | 9 | 23 | 11 | 3 | 0 | 14 | 5 | 11（10） |
| 17899-bug1 | 57 | 57 | 22 | 0 | 14 | 36 | 19 | 22 | 19 | 0 | 2 | 11（9） |
| 17967-pathA | 43 | 43 | 22 | 0 | 21 | 30 | 19 | 3 | 5 | 23 | 4 | 11（9） |
| 17967-pathC | 60 | 60 | 17 | 0 | 23 | 42 | 19 | 0 | 15 | 32 | 1 | 11（10） |
| 11741 | 10 | 10 | 0 | 0 | 0 | 1 | 6 | 0 | 10 | 1 | 0 | 36（27） |
| 17899-bug2 | 601 | 601 | 583 | 27 | 2 | 411 | 9 | 447 | 0 | 104 | 6 | 12（8） |

模式的含义（`graphdiff.classify`）：EDGE_CUT 种子里的一条消息或 WIRE 边没了（被故障的那次交换）；RETRY 同一个逻辑调用
又来一次（同一 site 重发、同类 occurrence 再现、故障节点自己的 daemon 多转一轮）；FALLBACK 出现了新的对端或新 region
的 occurrence（换一个 DataNode）；RECOVERY 同一节点在另一个 context 下把同样的活重做；STATE_DIVERGENCE 某个读改为读另一个
写者的版本；ESCALATION 故障 session 在 target 处观察到了 fatal 而种子没有；ABORT 不再到达 target；ANCHOR_DROPPED target 行
消失；DAEMON_INFLATION 两个以上节点多了 daemon 轮次（运行变长）；TOLERATE 除状态与决策外没有下游改变。

几点观察：

* 对照组几乎全是 TOLERATE（17897 的 11 个对照 session 全部 TOLERATE），说明上面的故障模式不是重放噪声。
* **ESCALATION 就是机制的见证**：七个 IPC case 里都有故障 session 直接在 anchor 观察到 fatal（pathB 25、bug1 19、
  pathA 19、pathC 19、17897 11、bug3 11、bug2 9），COMPOSE 选中的就是其中之一，CONFIRM 重放它本身。
* **IPC 故障对 DataNode 链路的影响以 RETRY / RECOVERY / FALLBACK 为主**：17897 里 FALLBACK 13（client 改试下一个 DN，
  即 13.3 的 GROW）；pathA/pathC 的 RECOVERY 21/23（同一个 DN 在新的 DATA_XCEIVER 连接里重做传输）。
* **bug2 的 601 个故障 session 里 ABORT 447、RETRY 583**：SPS 的 RPC 被故障打断后轮询重试，多数 session 走不到 target，
  这正是它 world 数最多、却只有 9 个 ESCALATION 的原因。
* **11741 的 10 个故障 session 全部 EDGE_CUT + ANCHOR_DROPPED**（其中 6 个另有 ESCALATION）：故障让 balancer 这次的
  调度 occurrence 消失，但它的结论是 CLOCK_SKEW，被移动的是两个时钟而不是故障标记；它的 16 个 GROW 也全部来自时钟翻转
  （CLOCK 门），不是故障。

GROW 由哪个门暴露（同一输出）：

| case | GROW | 其中故障 world | 被捕获为 task | 暴露它的门 → 节点上的新 occurrence |
|---|---|---|---|---|
| 11741 | 16 | 0 | 16 | CLOCK → balancer `SaslDataTransferClient.getUserNameFromEncryptionKey` ×8、`Dispatcher$1.run` ×4、`Balancer.matchStorageGroups` ×4（新的 balance-block anchor） |
| 17897 | 2 | 2 | 2 | IPC:RESPONSE:SocketTimeout → client `getUserNameFromEncryptionKey`；SASL:REQUEST → dn0 `getUserNameFromEncryptionKey`（13.3） |
| 17899-bug1 | 1 | 1 | 1 | IPC:REQUEST:ConnectTimeout → nn0 心跳处理 `PBHelper.convert` |
| 17899-bug2 | 7 | 7 | 6 | IPC:REQUEST+IPC:RESPONSE → sps `getUserNameFromEncryptionKey` ×2（新的 satisfy-storage-policy anchor）；IPC:REQUEST:ConnectTimeout → nn0 `PBHelper.convert` ×1；IPC:RESPONSE → sps `getUserNameFromEncryptionKey` ×1 … |
| 17899-bug3 | 1 | 1 | 1 | IPC:REQUEST:ConnectTimeout → nn0 `PBHelper.convert` |
| 17967-pathA | 2 | 2 | 2 | IPC:REQUEST → nn0 `PBHelper.convert` ×2 |
| 17967-pathC | 1 | 1 | 1 | IPC:REQUEST:ConnectTimeout → nn0 `PBHelper.convert` |

除 11741 外，每一次 GROW 都是故障 world 暴露的：要么是故障后的重试或换节点路径（`getUserNameFromEncryptionKey` 在
新的 SASL 握手里），要么是 DataNode 心跳重连后 NN 处理一条录制里没有的心跳请求（`PBHelper.convert`，其中超出录制轮次的
已由 tick bound 拦下，这里剩下的是轮次之内的）。

### 13.5 搜索空间会不会爆炸

每一波的增长有三个来源：新 world（每个 ADMITTED 的翻转 session 成为一个 world，路径在下一波再提供翻转）、GROW
（故障 world 走进录制里没有的 occurrence）、daemon tick（重放比录制慢，心跳多跑几轮）。理论上一条路径 F 个门或分支、
嵌套深度 3 就是 O(F³) 个 world，再乘每个 task 32 条路径、每个 anchor 64 个 task，确实可以爆炸。实际上被这些压住：
义务按"守卫 + 它依赖的输入"去重；corpus 能证明没有 world 走另一臂时直接 UNSAT、不重放（11741 的 418 个义务里 372 个）；
world 深度 ≤ 3；tick bound；12 波预算（DIAGNOSTIC）。

实测：九个 case 全部在预算之内到达不动点——七个 3–4 波，11741 7 波，17899-bug2 9 波（v90；被重启打断的 v88 是
11 波）。bug2 压力最大：v90 的 world 1 → 33 → 240 → 268 → 441 → 479 → 486 → 493，义务 47、274、34、215、104、27、
72、27、0（v88：45、298、9、200、123、44、62、59、41、7、0，world 到 484），从 W2 起全是
故障门翻转，落在 satisfy-storage-policy 请求里 SPS 轮询 NN 的 RPC 门上：每个故障让轮询重试，重试是新的 occurrence 和
新的门；它们在声明的请求 scope 内，不是 daemon tick，tick bound 不管。增量逐波变小，最后自己收敛，没有无界增长。要更早
收住它，需要一条"请求 scope 内重复 occurrence"的通用 bound，同时保留故障引发的重试本身（待定）。

先"爆"的是规划器实现：bug2 每波规划 20–25 分钟。线程栈全部落在两处按 session 线性扫描：`Frontier` 对每条路径的每个
决策重算 `Corpus.feeders`；`ClosurePlanner.carriersOf` 每跟一个读就扫一遍所有 session 的全部写。两者的结果都与 session
无关，总代价却随 session 数平方增长。`ff4db3a64` 改为建索引时算好。wave 9 的精确输入（765 个 session，从
`sessions-before.txt` 重建，`slots.jsonl` 复制而不是链接——规划器会写它）离线 A/B：旧 26 分 18 秒、新 3 分 34 秒，义务、
task、GROW、gap、图、manifest 六个文件逐字节相同。COMPOSE 在同样的语料上也有同类的平方项：`Corpus.roots()` 每问一次
就把所有 session 的 root mint 复制一遍，`Arms.Rows.varied` 再逐个 session 查值，而两者都按每个臂、每个 root 被问
（`f09f724e6` 改为只建一次）；它之后，COMPOSE 里互相独立的 z3 求解（每个 valuation、每条路径的自检）改为最多 8 个
并行（`b9483fb8f`）。

**探索的初衷是声明的那一个 (r,c,i)**（老板 2026-09-28）。fatal query 是一个 occurrence 的 target 行：种子重放时由 case
声明的 selector 解析成确定的 (r,c,i)，COMPOSE 的 φ 只取它的 target 行，跨进程的家族与臂也沿着围绕它的图配对。
可是在它已经出现 fatal 之后，探索仍在继续：bug2 的声明 occurrence（target-dn 上 `REGION.7c569c3f`，anchor 是
satisfy-storage-policy 请求）在 **W0** 就有 3 个被接受的重放观察到 fatal，之后又跑了 8 波、800 个义务，GROW 长到了
新的 satisfy-storage-policy 请求实例上；11741 的 dn1 `REGION.7c569c3f`（balance 的 SASL 处理）在 **W1** 就观察到 fatal，
之后又跑了 5 波。dn1 挂了之后 client 怎么重试、balancer 怎么重新调度，SPS 怎么起新的请求，都不是这个 bug 的问题。
`region_path_stop_at_fatal=true`（`970f9631f`，case 级开关，只给这两个 bug 打开）：一旦某个被接受的聚焦重放在声明的
occurrence 的 target 行上观察到 fatal，这一波就不再提出义务、不再 GROW，用一条 DIAGNOSTIC gap 点名见证，manifest 记为
WITNESSED，campaign 直接在已有的语料上 COMPOSE 与 CONFIRM。第一次这样跑时（v93 的 bug2）结论 MARKER_FLIPPED 且
CONFIRM 为真，却被一条 BLOCKING 扣下：闭包在 64 个 task 处截断，7 个 target-dn 心跳 IPC 门没有规划。截断的闭包对
"闭包上的结论"不健全，所以它平常是 BLOCKING；停在见证处的 case 不再对见证之后的闭包提问，和"只有种子跑过的
occurrence"在那里是 DIAGNOSTIC 同理（`21c42559d`：ClosurePlanner 只陈述截断了什么，由 ExploreMain 定级）。结果：
11741 在 W2 判为 WITNESSED（152 个义务，v88 是 418），bug2 在 W1 判为 WITNESSED（47 个义务），结论与完整探索时相同。

### 13.6 a10：52 个 ad-hoc case 全量重跑

a10 在 p109 上跑了全部 52 个 case，48 个跑完；4 个被集群重启打断，与另外两个被工具状态挡住的 case 一起在 p111 上
重跑为 a10c。**没有新 bug。** 结果按挡住它的第一个原因归类（`~/gc-out/analysis/triage.py`）：

| 类别 | case 数 | case |
|---|---|---|
| CLOCK_SKEW，CONFIRM true（接受：时钟同步的设计前提） | 2 | token-expired.TestFailoverWithBlockTokensEnabled-ensureInvalidBlockTokensAreRejected、token-pw-expired.TestFailoverWithBlockTokensEnabled-ensureInvalidBlockTokensAreRejected |
| 公式在录制取值下即 SAT（假阳性，被自检扣下） | 1 | commit-gs.TestClientProtocolForPipelineRecovery-testGetNewStamp |
| MARKER_FLIPPED 被扣下：同一 world 的重放把同一 consumer 配给不同生产者（调度未守住） | 1 | token-nokey.replicate |
| 所有组合路径在任何根取值下都 UNSAT（诚实否定） | 17 | commit-blockid.flush、commit-gs.TestFileAppend-testAppend2Twice、commit-gs.TestFileAppend-testAppendTwice、commit-gs.TestLeaseRecovery-testLeaseRecoveryAndAppend、commit-gs.softlimit、lease-missing.TestLeaseRecovery-testLeaseRecoveryAndAppend、lease-missing.softlimit、reader-chunk.TestFileConcurrentReader-testUnfinishedBlockRead、reader-chunk.flush、reader-chunk.reconstruct、recv-offset.mirror、sender-gs.mirror、sender-gs.reconstruct、token-blockid.TestFailoverWithBlockTokensEnabled-ensureInvalidBlockTokensAreRejected、token-blockid.proxy、token-nokey.TestFailoverWithBlockTokensEnabled-ensureInvalidBlockTokensAreRejected、token-nokey.TestFailoverWithBlockTokensEnabled-testFailoverAfterRegistration |
| 路径全 UNSAT 但闭包截断，否定不完整 | 1 | commit-gs.flush |
| 未陈述的读（INITIAL 版本 / 工具经由 JDK 的状态） | 10 | ack-seqno.flush、finalize-gs.TestClientProtocolForPipelineRecovery-testGetNewStamp、finalize-gs.TestTransferRbw-testTransferRbw、finalize-gs.flush、finalize-gs.mirror、pipeline-reply.flush、sender-gs.TestClientProtocolForPipelineRecovery-testGetNewStamp、sender-gs.TestDataTransferProtocol-testOpWrite、sender-gs.flush、visible-gs.TestFileConcurrentReader-testUnfinishedBlockRead |
| φ 为具体值：守卫的操作数不在版本化范围内 | 9 | addblock-notreplicated.softlimit、lease-holder.TestLeaseRecovery-testLeaseRecoveryAndAppend、lease-holder.flush、lease-holder.softlimit、reader-header.flush、recv-offset.TestDataTransferProtocol-testOpWrite、recv-offset.flush、stream-offset.flush、token-password.TestFailoverWithBlockTokensEnabled-testFailoverAfterRegistration |
| 没有 session 走到声明的 occurrence（种子重放时序） | 6 | commit-gs.TestFileAppend2-testSimpleAppend、complete-uncommitted.flush、token-blockid.mirror、token-nokey.mirror、token-password.mirror、token-pw-expired.mirror |
| NO_SUPPORTED_WITNESS：被选路径的 fatal 来自慢重放里真实过期的 token | 2 | token-expired.mirror、token-expired.proxy |
| 种子重放没到 target，campaign 在 REPLAY 失败 | 3 | close-retries.softlimit、visible-gs.TestClientProtocolForPipelineRecovery-testGetNewStamp、visible-gs.flush |

共 52 个 case。

**被接受的发现**：token-expired / token-pw-expired × TestFailoverWithBlockTokensEnabled，CLOCK_SKEW，CONFIRM true——HDFS
"各节点时钟大致同步"的设计前提，不是新 bug（§12）。

**假阳性过滤的新实例（commit-gs.TestClientProtocolForPipelineRecovery-testGetNewStamp）**：检查是
`FSNamesystem.commitOrCompleteLastBlock` 里 NN 存的 GS 与 client 提交的块 GS 不一致。φ = `not((GS@v125 − 1001) = 0)`，
录制里 GS@v125 = 1001，走健康臂。COMPOSE 为这次读建了一个 STATE family，两个 writer 臂：一个交付 1001（录制实际读到的），
另一个交付 1002（同一会话里 pipeline recovery 写的新 GS，`attested`）。模型在**没有移动任何根**的录制取值下选了 1002 的臂，
φ 为真——§11 的共享字段 HB 过近似：读被允许配上一个它在这次运行里并没有读到的写。DECIDE 的自检
FORMULA_SAT_AT_RECORDED_VALUATION（BLOCKING）把整个组合扣下，另外 5 个故障 world 里的 SAT valuation（各移动一个故障标记，
都选 1002 的臂）也因此不发布。与 §11 的 TestFileAppend2 不同，这一例在 COMPOSE 的自检就被拦下，没有走到 CONFIRM 重放。

**重放在同一 world 里不稳定、结论被扣下（token-nokey.replicate，a10c）**：探索 5 波（22、39、25、28、24 个义务）之后，
COMPOSE 得出 MARKER_FLIPPED——翻转 DATA_TRANSFER SEND 门（`Sender.send`，`REGION.2edcf422`）的故障标记后，目标 DN 的
`BlockPoolTokenSecretManager.checkAccess` 找不到 token 的 block key。它没有发布：骨架表（`slots.jsonl`）记下 consumer
`88df6241745a709a` 在某个 world 里由生产者 `d7692855e1139f0f` 服务，而同一 world（同一组翻转）的另一次重放
`ba1040a9e48c8c11` 把它配给了 `41161327159546b8`。同一组翻转下一个 consumer 有两种配对，是替换而不是生长
（DESIGN4 §3.3c），说明这次重放的调度没有守住：两个传输连接谁先被服务，在这个 world 里并不确定。COMPOSE 不从这样的
session 取行，30 条 TOPOLOGY_DIVERGENCE（BLOCKING）把 claim 扣下，没有进入 CONFIRM。它既不是被证实的 bug，也不是被证实的
假阳性，而是"微妙的并发让重放给不出唯一拓扑"的真实例子；这棵树本身带着 17967 的 key 轮换问题，这个 claim 很可能是那一类
已知机制在 replicate 工作负载上的出现。

**这一轮暴露并修掉的引擎缺陷**（main，通用修复，均跑过 `mvn -q -o clean package` 与 shell 测试）：

1. `ff4db3a64` 规划器按 session 线性扫描（13.5）。
2. `9ce0cc6c4` GraphChecker 自己的等待表与帧被当作程序状态发行：应用引用做 key 之后 VM 就给它版本，
   pipeline-reply.flush 里 271 条写是 `TimedWaits` / `Identity$Level` 的，同一次调用里读写 send 计数器成了 BLOCKING 的
   TOPOLOGY_DIVERGENCE。按会话核对，没有任何应用 site 读写这些位置；九个 case 的语料里为 0。现在工具自身包的读写不发行。
   工具经由 JDK 间接产生的状态（`ThreadLocal$ThreadLocalMap.set`，ack-seqno.flush 里 `INSTANCE/289#24` 被读数百次）
   按包名过滤覆盖不到：在 p111 上重跑（a10c）后，这两个 case 里工具自身代码的写行降为 0，但 TOPOLOGY_DIVERGENCE 还在，写者换成了两类不是应用语义、按包名又过滤不到的状态：pipeline-reply.flush 是 `java.util.HashMap#removeNode`，帧在 DATA_TRANSFER RECEIVE 门织入的 `PBHelperClient.vintPrefixed` 之下（`vintPrefixed` 本身只读一个 varint，这次 remove 来自门的运行时）；ack-seqno.flush 是 `sun.misc.Cleaner#add`——JDK 为 direct buffer 登记 cleaner 的全局静态链表，各线程分配 direct buffer 的先后每次重放都不同。完整的修法要按最近的非 JDK 调用者给事件归属（工具调用的 JDK 代码算工具），并把 JDK 自身的全局簿记排除在共享状态之外；列入下一步。
3. `d0a803fa1` worker slot 先认领义务再等本机内存：lift08 被 bug2 规划器占住 15 GB 时，TestFileAppend2 的一个义务在那里
   等了 30 分钟，另外八台各有 26 GB 空闲。现在先等到本机有空间再认领，队列被取空就退出；shell 测试新增"一台主机满载，
   整波全部落到另一台"。
4. `f09f724e6` COMPOSE 里 `Corpus.roots()` 与 `varied` 按臂、按 root 反复重建（13.5）：同一份 bug2 语料上，旧版跑了
   71 分钟还在构造臂，新版 30 分钟时已经在逐个 valuation 求解。
5. `b9483fb8f` COMPOSE 里互相独立的 z3 求解串行：现在最多 8 个并行、按原顺序读回，claim 与 gap 不变；Z3 的计数与错误集
   可并发共享，错误按排序报告。
6. `970f9631f` 与 `21c42559d`：case 级的 `region_path_stop_at_fatal`，以及见证之后的闭包截断不再扣下见证（13.5）。

**仍然挡住 ad-hoc case 的原因**（按引擎工作排序）：

* 未陈述的 INITIAL 读（finalize-gs ×4、sender-gs ×3、visible-gs、ack-seqno、pipeline-reply）。finalize-gs 的根因比 §12
  更具体：挡路的是 `DataSetLockManager$LockMap.getReadLock` 的锁表读，这张表在 DN 启动时（窗口外）填好，锁名由 blockId
  派生，所以与 φ 相关、被独立性保留。CLOSURE-V2 §3 规定这类只有 INITIAL、没有授权根的链应当 pin 成录制值；运行时没有为
  窗口外写入的版本发读行（SYMBOL-SCOPE 第 1 步的 Open 项）。即便修好，finalize-gs 在这些工作负载上也出不了 bug：φ 比较的
  是同一个副本对象的同一个 GS 字段，只有并发的 pipeline recovery 往 volumeMap 放新副本时才可能成立。
* φ 为具体值（lease-holder ×3 的字符串 holder、recv-offset ×2 的包头 offset、stream-offset、addblock-notreplicated、
  token-password）：VM 只给 int/long 字段版本。
* 种子重放依赖墙钟：token-*.mirror 在 head DN 收块时 token 已过期（工作负载把 token 寿命设成 1 分钟）；visible-gs.flush
  在 `DATA_XCEIVER#2` 提前关闭后，16 s 一次的放弃累计超过 65 s 的 ack 超时；close-retries.softlimit 的 lease 被第二个
  client 接走。
* 闭包截断（commit-gs.flush：52 条路径全部 UNSAT，但闭包在 64 个 task 处截断，否定不完整，BLOCKING）。

## 8. 下一步

**2026-09-28 这一轮留下的**（§13）：

1. **窗口外写入的状态要 pin**：只有 INITIAL 版本、没有授权根的容器读（finalize-gs 的锁表、sender-gs 的数组）应按
   CLOSURE-V2 §3 取录制值，运行时要为它发出带值的读行（SYMBOL-SCOPE 第 1 步的 Open 项）。
2. **工具经由 JDK 产生的状态**：门运行时里的 `HashMap.removeNode`、`ThreadLocalMap.set`，以及 JDK 自身的
   `sun.misc.Cleaner` 链表，不是应用语义；事件要按最近的非 JDK 调用者归属，JDK 的全局簿记排除在共享状态之外。
3. **请求 scope 内的重复 occurrence**（bug2 的 SPS 轮询重试）需要一条通用的 bound，同时保留故障引发的重试；
   `region_path_stop_at_fatal` 目前只对声明了单一 (r,c,i) 的 case 打开。
4. **两波之间的串行段**：规划器与导入检查只在 head 上跑；GROW 重跑也只在 head 上并行（11741 每个重放 6 GB，head
   一次约放 4 个）。

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
