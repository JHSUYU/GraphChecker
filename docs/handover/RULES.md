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
3. Write the state, the per-system TODO, the rules, the agent method, the tools and servers, and the
   design into the docs: [STATE.md](STATE.md), [TODO.md](TODO.md), this file,
   [AGENTS.md](AGENTS.md), [OPERATIONS.md](OPERATIONS.md), [../design/](../design/README.md).
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
- **The checks are the study's points.** `study.txt` (branch `study`) lists the ad hoc coordination points with
  their cluster tests; checks are those points, fine-tuned only, plus bug_study bugs that are real (hard to
  recover, verified in the system's code), ad hoc coordination, and checkable: the whole causal path and its
  symbolic propagation reach the `.smt` (an IO step that breaks propagation disqualifies a bug). A truly
  high-quality bug without a cluster test may get a self-written one. One GraphChecker branch per system
  (`system/<sys>`, the same body, small per-system adaptations). Order: HDFS, Solr, HBase, ZooKeeper.
- **The narrowed selection** ("这些地方优先选择和control plane有交互的", "可能check的case多于我们的点位…这是好事"):
  HDFS 38 points / 36 checked, Solr 21 / 13, HBase 30 / 17, ZooKeeper 13 / 10; points that interact with the control
  plane, that GraphChecker covers, with a high-quality cluster test; every known bug stays a check; one point may
  carry several checks. The lists are `selection.txt` on branch `study`; HDFS's are `experiments/hadoop/hdfs-adhoc/
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
- **A reasonable exploration bound, rarely touched** (owner 2026-10-05: "当然，我允许给一个合理的exploration的bound。如果过这个bound我们合理停下。但你不能大量的case都是触碰到这个bound"): exploration may stop at a declared, deterministic bound (a nesting depth, an obligation cap) and then publishes its formula with the bound named (a bounded verdict, visibly marked); reaching it must be rare. Every round counts the cases that touched it; more than a few is a defect (closure size, redundant obligations, slowness) fixed by a general rule, never by raising the bound per case. Running out of the time budget is not that bound: it is a run too slow (EXPLORATION_CUT, a named defect).
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
  Slowness from ten busy lifts is understood; the final acceptance runs each case alone on the whole cluster
  ("最终我们每个case挨个跑，每个case独占集群，那才是最终实现").
- **Agents** ("具体写代码coding agent最多4个。读，reveiw的可以稍微多点。但是reveiw要在关键，复杂的地方采用"): see [AGENTS.md](AGENTS.md).

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
- **Refactor bloat along the way** in the same commits as the goal work that touches it.
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
- **Lock, then one change at a time:** keep the last all-passing main; integrate one large change
  per live round; stacking several big changes is what made rounds regress repeatedly
  (2026-10-01).

- **Establish from the code what is done and what is not** (owner 2026-09-29): before claiming a capability,
  read the code (read-only agents may help); keep `docs/STATUS.md` (done / partial / not done per requirement)
  current.
- **Outcomes, not reports** (owner 2026-09-30/10-04): no report documents as deliverables; a check is done when
  its `.smt` is right. Agents report in a few lines.
- **The servers** (owner 2026-09-28/30): every fan-out (obligations, rounds, sweeps, builds) uses all ten lifts
  `lift06`–`lift15`, `lift11` included as a worker; no lift above 70 % memory (the host ledger enforces it;
  stop or move work past it); kill orphan z3 processes. Details in [OPERATIONS.md](OPERATIONS.md).

**Acceptance**
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
