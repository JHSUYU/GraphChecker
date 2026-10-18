# The owner's standing rules (long-term)

**Every agent that works on GraphChecker takes these rules as its own long-term memory**, the lead
and every coding or review agent alike. The owner, 2026-10-04: "长期记忆也要写明白。让别的coding agent也设为长期记忆".
They override any default. Where a rule quotes the owner, the quote is the rule; the English says
how it is applied. The owner's notes are also kept one fact per file in
`~/.claude/projects/-u-vnr3ne-GraphChecker/memory/` (index `MEMORY.md`). That directory and this file
say the same; this file is the one other agents read.

**Handing over** (owner, 2026-10-04 night): when the owner says stop, do these in order:
1. Stop every agent and every run (`tools/rounds/stop-run.sh`).
2. Have each agent commit its WIP and report its state.
3. Write the state, the per-system TODO, the rules, the agent method, the tools and servers, the checking
   method and its traps, and the design into the docs: [STATE.md](STATE.md), [TODO.md](TODO.md), this file,
   [AGENTS.md](AGENTS.md), [OPERATIONS.md](OPERATIONS.md), [PARALLEL.md](PARALLEL.md), [CHECKING.md](CHECKING.md),
   [../design/](../design/README.md).
4. Update the memory notes.
5. Delete outdated documents ("不用的旧文档都全部删掉").
6. Commit and push when the owner asks.

The README is only an index into these files ("如果readme放不下，可以readme给个目录索引，然后指到别的文档去").


The owner is a PhD student doing academic research on open-source system stability. Reply to the
owner in **Chinese**, answer a direct question first (before continuing the work), keep answers
short. The design decisions are the lead's (the agent coordinating the work), made after reading
the code; implementers follow a written design. **The lead decides engineering questions without
asking** (priorities, which agent takes what, resuming parked work, merge order: "之后这种权限我都给你，
刚刚这种不要再问"), acts, and reports what it decided. Decisions that change what the owner asked for
(the bug checks, the recording window, what counts as a root) and pushing go to the owner with a
recommendation.

**The 2026-10-02 goal's rulings**
- **Symbolic scope first** (sharpened 2026-10-04, below): widen the scope generally so more checks are flippable;
  per-system fine-tuning only, never per case.
- **Checks are real bugs**, each verified in the system's source, marked in its tree with
  `@CausynthExceptionTarget`, one campaign each; a self-written cluster test may be the workload of a truly
  high-quality bug; a low-quality bug is skipped.
- **IO rule:** a bug whose causal chain crosses file or HDFS-namespace state is not forced; a system's
  protocol header may be extended to carry the causal context (HDFS `RpcHeader.proto`, HBase `RPC.proto`).
- **Acceptance per check:** a SAT `.smt` whose claim has the bug's mechanism, confirmed, its chain checked by
  hand against the code.
- **Clean as you go:** unused code, artifacts and docs are deleted, not kept "just in case".
- **Java 1.8 for every system** ("整体system都要在java1.8版本上"): every tree and workload builds and runs on JDK 8
  (the VM is OpenJDK 8 Zero); verify it first in a new system's feasibility phase.
- **Workloads are the system's existing unit tests where possible** ("zookeeper, hbase这些worklaod尽量都利用已有的unit
  test。然后手动修改communication protocol。插hook。小的workaround手动改一点是允许的。但尽量general"): search the test tree
  first; protocol headers and hooks may be added by hand; a self-written test only when no existing test
  reaches the bug (say why in STATUS).
- **An early recording window is opt-in per case** for a bug whose fatal value is set during cluster startup
  (`recording_window=startup`, HBase #14; owner 2026-10-03); every other case keeps the window opened once the
  cluster is up.
- **Second-tier bugs are not a TODO** (owner 2026-10-03).

**The 2026-10-04 goal's rulings** (owner, long-term; each one quoted)
- **The checks are the study's points.** `study.txt` (`docs/checks/`) lists the ad hoc coordination points with
  their cluster tests; checks are those points, fine-tuned only, plus bug_study bugs that are real (hard to
  recover, verified in the system's code), ad hoc coordination, and checkable: the whole causal path and its
  symbolic propagation reach the `.smt` (an IO step that breaks propagation disqualifies a bug). A truly
  high-quality bug without a cluster test may get a self-written one. One GraphChecker branch per system
  (`system/<sys>`, the same body, small per-system adaptations). Order: HDFS, Solr, HBase, ZooKeeper.
- **The narrowed selection** ("这些地方优先选择和control plane有交互的", "可能check的case多于我们的点位…这是好事"):
  HDFS 38 points / 36 checked, Solr 21 / 13, HBase 30 / 17, ZooKeeper 13 / 10; points that interact with the control
  plane, that GraphChecker covers, with a high-quality cluster test; every known bug stays a check; one point may
  carry several checks. The lists are `docs/checks/selection.txt`; HDFS's are `experiments/hadoop/hdfs-adhoc/
  checks.tsv` (46 HDFS cases with the 10 named ones).
- **Swap the too-challenging** ("要是哪几个case实在是过于challenging。就从备选里挑一个质量也不错的。容易搞定的换上来"): a
  check still a RUN_DEFECT after a reasonable fix round is replaced by a good, easier alternate, counts kept (HDFS:
  05, 06, then 04, then 38/45); each swap updates `checks.tsv` and `selection.txt` with the reason.
- **System by system** ("hdfs所有的case跑完为一组，不要有回归。然后就到另一个系统", "下一个系统跑的时候就不要再管别的系统的事了"):
  one system's whole group runs until it has no regression; nothing of another system is touched meanwhile.
- **Symbolic scope is the top priority** ("你必须要合理扩大符号范围。让更多的都可翻转"): the selection stays automatic and
  general; widen it so more checks are flippable. **Control flow counts as much as data flow**
  ("if(obj.fieldA){xxx} xxx有data flow在，那obj.fieldA理应也作为符号的一部分被纳入"): a branch deciding whether slice code
  runs makes its operands symbols, inside a method, along the call chain and at callers. **IO only on the traced
  flow** ("io肯定也是要能在我们data flow整个流程上的才考虑（包括rpc, 或者别的）。别的io肯定不考虑"): an IO operation is a
  counterfactual site only where its result or failure flows into what we trace.
- **Only SAT or UNSAT** ("unsat就是unsat。我们不是symbolic propagaiton+merge吗。拼出.smt。结果肯定不是sat就是Unsat啊。你符号化的
  就符号化，具体值的就具体值"): the composed `.smt` decides. The exported `candidate.smt2` is the full formula (the admitted
  paths' disjunction, roots free over their domains, the fatal arm asserted) and UNSAT is z3's unsat on exactly
  that file ("unsat这些至少都得是我们导出来了.smt吧"). A concrete value is a constant; a value that moves with a root is a
  free leaf, never a pin; a claim is never refused because a value is concrete. **Only SAT is validated**
  ("只有sat我们要经过validation"): CONFIRM plus a native reproduction. A witness moving no root is never SAT. A real run
  failure (the occurrence never ran, a self-contradictory path, a solver timeout, CONFIRM without a verdict) is a
  named RUN_DEFECT: a bug to fix, not a verdict.
- **A large closure converges; a bound is only a last-resort valve** (owner 2026-10-05: "当然，我允许给一个合理的exploration的bound。如果过这个bound我们合理停下。但你不能大量的case都是触碰到这个bound"; "有些case的 exploration过深。是真的因为闭包region很多而要很久。理论上我们当然希望所有闭包可以收敛，这种情况你也不能因为bound就把人家限死…毕竟我们单独跑这个case的时候有很多的集群资源，并行可以降低时间的"):
  - a closure deep because it is genuinely large must converge: give it resources (many obligations in parallel over all ten lifts, a longer case budget), never a cut; depth from redundant work (equivalent occurrences, re-asked arms) is an engine defect, fixed by a general rule;
  - the sweep's case time limit is a convenience of a shared cluster, not a verdict: a case cut there (EXPLORATION_CUT) is rerun alone to its fixed point;
  - a generous declared bound (a nesting depth, an obligation cap) may stop exploration as a last resort; such a stop is named in result.json, rare, counted every round, and each one is investigated (large or redundant).
  - **a genuinely large closure that does not converge may END by a bound** (owner 2026-10-12, Solr: "如果不收敛确实是因为闭包太大。可以给一个bound结束"): once the redundancy is fixed and new distinct arms still keep coming (not re-asks of one arm under many ids, not solves starved behind replays), a declared bound ends the case, BOUNDED and named in result.json; its STATUS row states the bound, where it stopped and what stays unasked, and the case counts as done.
- **A check is done when its `.smt` is right** ("如果我们确实正确的跑出了.smt。包含必要的因果链，符号变量，符号传播。没有新bug也是
  可以理解的"): the causal chain, the symbols and their propagation read against the system's code; no new bug is then
  an acceptable outcome.
- **Every change deletes what it replaces** ("每次这些你就要把旧代码，不用的代码，都删掉。我们也不需要保留fallback"): no
  fallback, no flag keeping an old path, no compatibility shim; old artifacts, snapshots and outputs are cleaned up
  too ("对不用的旧代码，旧产物，文件都清理了").
- **Workarounds, with measure** ("如果一个workaroud能解决一个巨大的工程改动，就是可以的…我们在做research artifcact。你也不能充斥着
  workaround。能general还是general", "不仅是符号选择。我们整个系统设计都要这样的"): across the whole design, a small manual
  change in the system's code is allowed when it replaces a huge engine change, at one general point, listed in STATUS
  "Per-system surface" with the checks it serves; never to force an expected mechanism; general engine rules first.
- **Every case should be fast** ("整体我们跑通每个case都会比较快。如果有的case特别久，那可能就是有问题了。你要去看一下，不要傻等",
  "如果你发现时间显著变慢，就要多看几眼了"): a case far slower than its peers or its history is investigated at once.
  Slowness from ten busy lifts is understood. The final acceptance does NOT need each case alone on the cluster
  (owner 2026-10-05: "我们不必强行要求独占。一定要最大化10个集群的使用。我们的核心目标是46个adhoc check先跑通出有正确因果链的.smt";
  this replaces the earlier "每个case独占集群"): cases run concurrently through the ledger; the goal is a right `.smt`.
- **Agents** ("具体写代码coding agent最多4个。读，reveiw的可以稍微多点。但是reveiw要在关键，复杂的地方采用"): see [AGENTS.md](AGENTS.md).

**The 2026-10-05/06 rulings** (owner, quoted) **and the lead's standing decisions** (the owner may overrule them)
- **The core goal** (owner 2026-10-05): "我们的核心目标是46个adhoc check先跑通出有正确因果链的.smt". A symbolic-scope
  hole is fixed now when the current formula is wrong or incomplete (a value the code puts on the chain is missing: a
  guard field that is not a symbol, a wire value unbound or HELD, a fatal arm that is a constant because its deciding
  branch is never asked); a widening that only makes more of a right formula flippable waits until the 46 are done
  (TODO HDFS §5 (B)).
- **Swaps used** ("32直接换成05吧"; "可以把个别特别challenging的换成我们能处理的"): 32 -> 05; 01, 17, 43 -> 06, 38, 45 (their seed
  replays never reached the target, with or without the time model). Of the swap rule's alternates only 04 is left.
- **The time-model family is relaxed** (owner 2026-10-06: "我要大幅放宽时间模型的那几个case。我允许为了跑通这几个case依赖
  workaround/只要差不多能跑通.smt就行了"): for 21 22 23 24 25 34 35 52 only, workarounds in the test cluster's
  configuration, the HDFS adapter or the system code are allowed to get a run through (TODO HDFS §2), and an
  approximately right `.smt` is enough: a `candidate.smt2` z3 decides, with the main causal chain in it; residual
  gaps (some seed give-ups, a few HELD values, a bounded round) are acceptable when named in STATUS. Still: no
  fabricated result, every workaround listed in STATUS, and no regression of the other 38 cases.
- **The time model is workarounds only, never ground on** (owner 2026-10-06, long-term: "好的，time model我现在全部workaround，
  不必死磕，设为长期记忆"; "时间模型整个都不用死磕。.smt能跑出来即可，即使小有问题也可以接受"): replay clock fidelity, seed
  give-ups from clock-driven turns (heartbeats, IBRs, the edit log's async claims) and the whole start-up/clock family
  are handled by workarounds (test-cluster configuration, the HDFS adapter, small system-code patches, listed in
  STATUS), never by engine work to perfect the time model; this also covers a non-clock case whose seed replay
  stalls on that timing. An approximately right `.smt` is enough there; no fabricated result; no regression.
- **Reasonable parallelism, not over-subscription** (owner 2026-10-06 afternoon: "你也不要过分并行哈。合理的并行。要不然反而会让速度
  变慢"): at ~18 live campaigns (four agents' gates plus the lead's rounds) every case ran 3-5x slower and heads starved for
  ledger room. Each agent runs at most 2 live campaigns at once (critical path first, offline gates where they answer);
  the lead's rounds are what a gate or the final round needs; about 8-10 live campaigns in all; a queue is paused rather
  than starved. Ten lifts pay most inside one case (its obligations fan out). The principle ("并行你要记住是让吞吐提升。而不是
  单单为了并行"): parallelism serves throughput -- cases finished and fixes validated per hour -- measured by each case's
  wall time against its solo history (round-slow.sh) and the ledger's waits, never by how full the lifts look.
- **Lock what is right; the rest on `system/hdfs1`** (owner 2026-10-06 ~16:00: "当前所有已经跑完.smt，时间用时合理。.smt也正确的代码就放到
  system/hdfs上。然后剩下的所有case。去system/hdfs1上处理。这样我们可以避免不断陷入regression"): `system/hdfs` is the locked body
  (only docs land on it); one locking round on it closes every case it can, each right `.smt` there final; every other
  change (codec capture, open arms, rule 1, the retried-call identity) and every case still open is worked on
  `system/hdfs1`, branched from the locked body. The end state is these two branches (owner: "最终就是两个分支，system/hdfs和
  system/hdfs1"): nothing merges back into `system/hdfs` or `main`; STATUS names the branch that closed each case.
- **The last open cases close by workarounds** (owner 2026-10-06 ~20:00: "如果加点workaround，是不是小改动就能大大省去我们的很多
  复杂改动"; "我要求你加点workaround"): where a general fix would be an identity, PLAN or runtime change gated on many cases,
  a per-case workaround closes the case instead -- a case declaration (its own loop bounds, world depth), or one small
  patch in a tree only that case reads, selected per case in its `case.sh` -- named in STATUS's per-system surface, with
  the general design written into TODO. Used: 21 (its handshake on a joined thread, tree `gc/hdfs-study-r7-21`;
  `parseVersion`'s loop bound 24), 07 (QJM's reply maps in logger order, tree `gc/hdfs-study-r8`; world depth 6). Never a
  fabricated result; the residue a workaround leaves is named in the case's STATUS row.
- **Parallelism is documented** ("你整个并行的思路要专门写到文档里去"): [PARALLEL.md](PARALLEL.md).
- **Checking is documented** ("尤其是你检查.smt效果踩过的坑，也要说清楚"): [CHECKING.md](CHECKING.md) is how every verdict and
  `.smt` is checked, with every trap a lead fell into. Nothing counts as done before it passes CHECKING §1.
- **A SAT is judged on the path it claims, an UNSAT on every path it rests on** (lead, 2026-10-06): cone.py gates a SAT
  on the claimed selector's fatal cone (other selectors' unbound handoffs are computed and reported as
  `unboundOffWitness`, never hidden); an UNSAT on every admitted path, and COMPOSE refuses to close while any path's
  cone holds an unattested handoff. Not a per-case or per-variable exemption.
- **A witness with an open chain is confirmed first, its chain grown meanwhile** (lead 2026-10-06 grew it first; owner
  2026-10-15, best effort and performance first): when the first witness's fatal cone names a HELD/unbound handoff,
  CONFIRM decides the SAT at once while EXPLORE grows only that chain's producers; a confirmed witness ends the
  exploration, a refuted one is attempted again over the grown corpus; an open chain is named (`WITNESS_CHAIN_OPEN` in
  EMIT's `defects[]`).
- **COMPOSE is best effort** (owner 2026-10-15): a defective session, path or part is left out and named
  (DIAGNOSTIC), the rest composed; only a total absence (no seed, no path) or SEED_OBSERVED_FATAL blocks.
  Exploration refusals stay (they shrink the work); a GROW re-run that did not finish is dropped, never re-run.
- **An arm the bug may live in is never closed silently** (lead, 2026-10-06): every open decider arm of
  a reached anchor that no admitted run took is named at the fixed point with its flips' verdicts; flips that only came
  back NOT_ADMITTED leave no verdict (`OPEN_ARM_UNANSWERED`, RUN_DEFECT).
- **A faithful run that never enters an open arm's occurrence refutes that world** (lead, 2026-10-06, after the
  handover; agent S's design A for 39/40, tightened after review): for an open
  arm's flip toward the arm only, a replay that ran its world faithfully -- every assignment minted and planted, no
  prefix abandoned, every inherited flip taken; no order hold gave way and no paired read misread (holds still waiting
  wait only on the never-entered occurrence); the world acted in the window (a plant at the recorded value is no act)
  and no slot was given up before it did; the workload ended by itself -- and never entered the flip's occurrence
  refutes that world (`WORLD_REFUTED`). The world is named and excluded from the arm's re-ask, never the arm; a refuted
  world is never re-run, at most past eight (named `bounded`); an UNSAT after it states what it rests on, and each
  refutation is read against the code before the UNSAT counts. Anything short of faithful stays NOT_ADMITTED/UNANSWERED
  (a RUN_DEFECT at the end, as the owner ruled for a run failure). Never applied to CONFIRM.
- **The engine's own plumbing is never program state** (lead, 2026-10-06, codec-capture design): no field of the engine's
  runtime package and no field of a generated protobuf message or builder (immutable once built) is a STATE location or
  a READ_SITE; a read made by such code takes its observed version's value at import.

**The 2026-10-17/18 rulings** (owner, quoted; long-term unless marked)

- **Each final case runs alone on the whole pool** ("我们还是要让case独占"): no cross-case concurrency in a final round;
  development and agents' offline runs stay off the pool while a final case runs (lift11 only), or the round is stopped.
- **A large rewrite is allowed, old code is gone for good** ("由于现在代码太过于臃肿，我已经允许你大改动了", "你可以大规模
  重写了，最后20个case重跑一遍debug就行", "旧的代码就要全部删除了。再也不用了"): one implementation per concept, no
  flag or fallback, nothing kept for comparison (references are old run outputs and old jars); acceptance of the rewrite =
  all 20 Solr cases rerun and debugged. The plan is REFACTOR-PLAN.md.
- **Read what exists before building** ("总之你好好读读现在已有的代码机制和细节吧，不要重复造轮子了 ... 包括system/hdfs
  上的上一个版本的代码，包括vm"): an inventory of the engine, both branches and the VM precedes a new mechanism
  (analysis/solr-2026-10-18/capabilities/INVENTORY.md).
- **Explore everything in principle, collapse duplicates soundly; the depth parameter stays** ("理论上我们当然想探索所有
  ... 你已经发现大多是重复的。那就把他们都处理好啊，正常探索", "成熟的concolic engine都有解决方案了", "不过深度参数还是
  要保留我要控制分支探索数量"): use focused replay's enforced prefix and the closure loop (not new machinery) with the
  generational bound; the owner sets the world depth.
- **Redundancy before distribution** ("优先排查planner的冗余能压缩多少。如果确实冗余太多能大量压缩，那我们就不用做分片了",
  "分片就先不做了"): session sharding is shelved; compaction gave the headroom.
- **Watch processes and NFS, never wait blindly** ("有太多zombie process以及nfs卡死的问题，你要监视着，尽早处理好，不要一直
  死等"): the watchdog (LESSONS.md §3) runs during rounds.
- **Handover by documents** ("如果我们token到了95%。就请你停下所有任务，把todo更新到文档里 ... 总结我们踩过的很多坑，性能
  优化看什么，debug我们的各种经验"): keep STATE/TODO/LESSONS current at every milestone; at a stop, agents checkpoint as
  gated commits + 'WIP (not gated)' commits on their branches.
- **Stay on the liftlab servers** (2026-10-18: "算了算了还是用liftlab的server吧"), Solr only for now ("hbase的当前不用做").
- **Refactor = delete dead code, easiest first; no deep rewrites** (2026-10-18 evening: "事实上降低代码行数也有利于我们之后开发
  不是吗。这样，我给你一个rule，重构主要就是删除死代码，以及优先做最顺手的重构。特别深的重构，重写可以不做"): fewer lines help later
  development; the work is dead code first, then the cheapest merges of duplicated concepts and line-reducing splits,
  ranked by lines saved per effort (the audit: analysis/solr-2026-10-18/loc-audit/AUDIT.txt); a deep redesign (e.g.
  run_engine.sh's scheduler in Java, a new SmtLowering) is not done.
- **No comments in the code** (2026-10-18 evening: "注释我觉得可以彻底删了。31k太夸张了"): the code carries no comments
  (Java, run_engine.sh, tools/, experiments/); what the code does and why is in docs/design. They are stripped once
  every branch of the rewrite is merged, proved by identical bytecode (`javap -c -p`) and identical `declare -f`;
  new code adds none. Shebangs and text inside strings or heredocs are data, not comments.
- **No byte-identity gate after the rewrite** (2026-10-18 evening: "由于我们改动很大。不再要求做语义一致逐字节比较。跑出.smt包含正确的因果链即可，小问题不用死磕"; "我说的validaiton是.smt给出sat后的重放"): a change is
  accepted when each case's `.smt` holds the right causal chain and a SAT is replayed -- CONFIRM in the VM (strict) and
  REPRODUCE natively; small issues are not ground on. This supersedes rule 5 of "Code health" below (its byte-identical gate)
  for the Solr rewrite.

**Engineering**
- **General fixes only.** No per-case code, no fixes derived from a case's expected verdict, no
  dead code, no fallback paths, no flags to keep an old path. Per-system code is allowed only as a
  small adapter or a declaration row, listed in STATUS "Per-system surface". Every stop/skip rule
  and every performance optimization is general.
- **Global view, read before you decide:** read all the code a concept touches (every stage) before
  a fix or a design choice, look further, decide from the whole ("做bug fix，design choice前。我建议你多阅读些
  已有代码，看的更远些，考虑整体"); fix the class of bug, not the instance. Docs may be stale — the code and
  the owner's current requirements are the reference. Verify a diagnosis in code before briefing an agent
  with it (this lead's wrong guesses cost hours: a VM image blamed for a hang that ran on stock HotSpot, a
  memory charge misread).
- **Refactor only when truly necessary** (owner 2026-10-11, long-term: "重构代码不要太频繁，在你认为真的有必要时再动手重构";
  this replaces the 2026-09-24 "refactor bloat along the way"): a refactor goes in only where the change cannot be made
  cleanly without it or a real bug class hides in the duplication; never as a side job of every touch. Deleting the
  code a change replaces or leaves unused stays mandatory.
- **Big strides, then debug** (owner 2026-09-23): for a large redesign, write the whole main body first (compile and
  unit-test only), then run campaigns and debug; do not interleave many small live rounds with half a design.
- **JVM-level relation preservation:** symbolic propagation is at the JVM level (shadows on slots,
  fields, objects), not KLEE's byte level. Every value moved outside interpreted bytecode is
  HOOKED, MODELED, or DETECTED-AND-PINNED by name — never lost silently. Shadows never belong to
  a JVM-shared identity (cached boxes, interned Strings, `Boolean.TRUE`).
- **No recorded-order pruning:** never drop candidate writers because they come after the read in
  the recording.
- **The question is one declared occurrence** `(r,c,i)` fixed at the seed; a campaign stops at its
  first witness when the case says so.
- **Lean tests:** table-driven, one test class per new class, delete tests of removed mechanisms.
- **Docs track the code:** docs describe HEAD only; update `docs/STATUS.md` and the design docs in
  the same commit as the change; delete what becomes outdated.
- **Time optimization never ends:** after every round, measure where each campaign's time went
  (`timeline.py`) and cut work that produced nothing, with a general rule, gated so verdicts do not
  move. A check should take tens of minutes; an occasional run past an hour is fine, but runs of
  hours usually mean a defect (a stall, a starved step, an exploding closure): find it.
- **A run that looks wrong is stopped at once and debugged, never waited out** ("用时过长的case往往都有问题…
  就不要盲目等待，及早停下开始debug"): a log silent for minutes, a stage far beyond its usual time, a host over its
  memory gate. Take a jstack, read the schedule and the ledger, name the cause in code. 2026-10-03 examples:
  a recording hung on an upstream Solr race; ZooKeeper writes admitted after they ran; an O(n²) re-import; a
  canary confined to one host.
- **The closure revolves around the declared target region `(r,c)`** (the seed graph too): prune
  branches that lost it; for HDFS only the target DataNode matters. Never encode a case's chain.
- **The closure keeps every static writer** of a demanded location; never drop writers the
  recording did not exercise (an untaken branch's write is what a flip enables). Over budget:
  recorded writers first, the rest cut by a named `PLAN_CLOSURE_CUT`.
- **Over-approximate, confirm strictly:** COMPOSE/EXPLORE may produce false SATs (CONFIRM refutes
  them, the model is excluded, the next claim follows); composer imprecision is a performance item,
  never a blocker. CONFIRM is the last filter and must stay strict (never loosen what it compares
  without an equal check; every substitution named). Completeness outranks precision: a guard
  that can make a real witness UNSAT is worse than a false positive.
- **Roots from general rules only;** a small per-system adapter is allowed and listed in STATUS
  "Per-system surface"; never a root chosen per case or by the expected mechanism.
- **Delete what automation replaces:** every automating merge deletes the old code, manual tools,
  hand rows and scripts it replaced.
- **Waits end** (2026-10-06): every background wait has a timeout and waits on a pid or a file; never `pgrep -f`
  on a string its own command line contains (it matches itself and never ends: a lead's and an agent's waits ran for
  hours), never a chain of waits on another wait's output.
- **Never wait blindly on many shells; look for stuck ones** (owner 2026-10-12, long-term: "对于同时跑的多个shell，你也不要盲目等待。
  合理的去看个别shell别被卡死了啥的"): at every check-in, and whenever a tool call or an agent is unusually slow, look at the
  shells as well as the runs: D-state processes on the control host and their `/proc/<pid>/wchan` (`autofs_wait`,
  `nfs_*`), the load, background waiters older than their purpose (a waiter on a stopped run whose summary never gets
  its verdict row, a file test on another host's `/tmp`). Fix the cause at once and kill the stuck ones by pid (the
  2026-10-12 `BASH_ENV=/sw` jam cost about an hour of every agent's time; OPERATIONS §8, PARALLEL §6).
- **Shell under `set -u`: initialize every local** (`local x=""`): an unset one errors the function and its callers
  retry forever (the ledger fix's first version spun the shell test, 2026-10-06).
- **Offline gates are started off `lift11`, a few cases at a time** (`onlift.sh`): dozens of `offline-ab.sh` waiters on
  one host jammed NFS (254 processes in D state on lift11, 2026-10-06; the ledger now refreshes a host's reading once).
- **Worktrees and snapshots leave out `third_party/`** (`tools/lib/worktree-add.sh`): 99 % of the repository's files are
  the VM's source; a full checkout on NFS took 45+ minutes and made every commit in it slow.
- **Lock, then one change at a time:** keep the last all-passing main; integrate one large change
  per live round; stacking several big changes is what made rounds regress repeatedly
  (2026-10-01). **Superseded across systems by per-system branches** (owner 2026-10-08, long-term: "solr上现在是全新的开发了。
  引擎和vm可以一次多处修改。不必遵循一次修改一处"; "不止局限于hdfs, 以后，hdfs, solr, zookeeper, hbase都是自己的branch。回归只考虑在自己的
  system内"): each system lives on its own branch (`system/hdfs` + `system/hdfs1`, `system/solr`, `system/zookeeper`,
  `system/hbase`) and regression is judged only within that system (Solr: its 20 cases, solr-18406 and solr-18413
  first, a final round of all 20 with none regressed). Several engine and VM changes may land per round; another
  system's corpora may serve as offline-gate data, never as a blocker.

- **Establish from the code what is done and what is not** (owner 2026-09-29): before claiming a capability,
  read the code (read-only agents may help); keep `docs/STATUS.md` (done / partial / not done per requirement)
  current.
- **Outcomes, not reports** (owner 2026-09-30/10-04): no report documents as deliverables; a check is done when
  its `.smt` is right. Agents report in a few lines.
- **The servers: MAXIMIZE all ten** (owner 2026-09-28/30, restated 2026-10-05 long-term: "一定要最大化利用10个server。这10个
  server配有nfs,你只要做好代码隔离等。可以大大加速的。这是你的长期记忆"): keep `lift06`–`lift15` (`lift11` included as a
  worker) full at all times. Every case or probe that does not wait on a pending fix runs now; a landed fix is validated
  at once on the cases it touches, never waiting for a whole round; check utilization (memory and load on every lift)
  at every lull and fill it. NFS shares everything, so isolation is what makes this safe: every agent and run on its
  own worktree, frozen snapshot and `GC_OUT`, never a tree or snapshot someone reads. The only limit: no lift above
  70 % memory (the host ledger enforces it; stop or move work past it); kill orphan z3 processes. Details in
  [OPERATIONS.md](OPERATIONS.md); how development keeps them full (levels, isolation and sharing, the loop):
  [PARALLEL.md](PARALLEL.md), part of every agent's long-term memory.

**Code health: delete redundancy; refactor only where truly needed** (refactoring: owner 2026-10-11, above; the rest: owner, goal of 2026-10-04 night: "代码可能现在有点臃肿。在你跑通hdfs
的同时，你也要删除冗余，不用的代码。并重构非常ugly的代码"; and "每次这些你就要把旧代码，不用的代码，都删掉。我们也不需要保留fallback",
"对不用的旧代码，旧产物，文件都清理了"). This is part of every goal, not a separate phase:
1. **Every change deletes what it replaces and what it leaves unused**, in the same commit: no fallback, no flag that
   keeps an old path, no compatibility shim, no "kept just in case"; the tests of a removed mechanism go with it. The
   commit message (or the agent's report) lists what was deleted.
2. **Dead code is found with evidence, never guessed**: bytecode reachability from the real entry points (the Java
   mains `run_engine.sh` and `tools/` launch, the hook methods `CausynthPipeline` weaves by name, the system trees'
   calls into `MessageDoors` and the shim, reflection, VM natives), then a grep over `src/`, `run_engine.sh`, `tools/`,
   `experiments/` and every system tree (`/bigtemp/vnr3ne/wt/hadoop-*`, `lucene-solr-*`, `zookeeper-*`,
   `hbase-unified`); config keys and environment variables no launcher sets; shell functions nothing calls; scripts no
   tool or doc names. The 2026-10-05 audit's tables: `/bigtemp/vnr3ne/analysis/study-2026-10-04/cleanup-audit/`.
3. **One mechanism per concept**: two implementations of one idea (a second "does this move" walk, two pairing rules,
   nine "property else environment" lookups, JSON helpers beside `smt/JsonFields`, a forwarding layer that only
   re-calls the next one) become one.
4. **Very ugly code is refactored when a change truly needs it** (owner 2026-10-11: not frequently): a method of more than ~150-200 lines or ~50 branches becomes named steps over one
   context object; parallel switch ladders become one table; a file that mixes responsibilities is split by them
   (`SmtLowering` -> `VmTermLowering` + `SmtSymbolTable`; `CausynthTraceRecorder`'s offline aggregation into its own
   class; `CausynthPipeline`'s weaves apart from the analysis orchestration). The code carries no comments (owner
   2026-10-18, above); history belongs in git.
5. **A refactor or deletion changes no result**: gated by `tools/regress/offline-ab.sh` with byte-identical outputs of
   every stage it touches (COMPOSE's `candidate.smt2`/`claim.json`/manifest, SEED.static), only named run-to-run noise
   excluded (`solverRuns`, `unsatCore`), plus `mvn -q -o package` and the shell test on every commit.
6. **No conflicts with live work**: clean up files no in-flight branch touches (a busy-file list from
   `git diff --name-only system/<sys>...<branch>` of each open branch), the rest after the merges.
7. **Artifacts too**: merged branches and their worktrees, stale snapshots (`tools/rounds/snapshot-gc.sh`), finished
   agents' outputs, outdated documents are deleted; evidence still needed is named in STATE.
What is still owed: TODO.md HDFS §7.

**Acceptance**
- **How to check**: [CHECKING.md](CHECKING.md) (round-verify's columns, the hand check with the legend, the traps).
- **What a real PASS is:** the claim, polarityDecides, the mechanism's roots in
  `claim.movedRoots`, confirmed, cone gate — a PASS line or a finding kind alone is not acceptance.
- **Mechanism mandate:** 17899 bug1/2/3, 17897, 17967 A/B/C are MARKER_FLIPPED by an IPC door
  fault (either direction); 17960 by its config; 11741 by clocks (or a fault); the Solr cases by
  clocks (CLOCK_SKEW).
- **After every engine change, check the `.smt` causal chains** of the cases it can touch against
  the system code (e.g. 11741: `allKeys` ite/put/remove, keyId across the wire, the solver's
  choice).
- **Real false-positive examples only:** never construct false positives; FP-filter examples come
  from real runs.

**Git and safety**
- **Push only when the owner asks** (each request covers that moment, not later commits). Never
  `git add -A`. Commit only when the change is built and tested.
- Before every commit: `mvn -q -o package` and `bash src/test/shell/run_engine_campaign_helpers_test.sh`
  (both via `onlift.sh`, [OPERATIONS.md](OPERATIONS.md)).
- Commit messages end with `Co-Authored-By: <model> <noreply@anthropic.com>`. Commits in the
  Solr/HDFS trees use `git -c user.name="Zhenyu Li" -c user.email=zhl136@ucsd.edu`.
- Never edit the owner's dotfiles. Never rebuild a tree or edit a snapshot a campaign runs on.
  Never remove a `~/gc-run/p<N>` a running round uses: `tools/rounds/snapshot-gc.sh` removes one
  only when no process on any lift names it.
- Solr's test SecurityManager may be changed if it interferes (owner's permission); today it is
  off via `-Dtests.useSecurityManager=false`.
