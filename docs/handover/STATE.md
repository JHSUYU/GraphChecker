# State at the handover of 2026-10-06

The owner stopped the lead and every agent ("请你停止所有在做的agent任务，跟之前一样。把todo, design，agent合作方式，所有的长期记忆，
开发踩过的坑…能让别的agent快速接手。同时，把commit push到远端"; "尤其是你检查.smt效果踩过的坑，也要说清楚"). Nothing runs on
any lift: every agent stopped its runs and committed its WIP on its branch; the lead stopped its last check (HG10V).
Read this file, then [TODO.md](TODO.md), [RULES.md](RULES.md), [CHECKING.md](CHECKING.md), [AGENTS.md](AGENTS.md),
[OPERATIONS.md](OPERATIONS.md) and [PARALLEL.md](PARALLEL.md). The design is in [../design/](../design/README.md);
every check with its live state is in [../checks/README.md](../checks/README.md); done / partial / missing per
requirement in [../STATUS.md](../STATUS.md).

## 1. The goals (verbatim) and what they mean

The 2026-10-04 goal (the four systems):

> 请你阅读graphchecker的source code和vm代码。先了解这个Tool在处理的adhoc coordinaiton。以及我们的处理方式。然后阅读graphchecker远端study分支上的study.txt。里面记录了4个system的adhoc coordianotin位置，以及他们对应的cluster based unit test。同时，~/bug_study下是一些可能是adhoc coordianot有关的bug。请你仔细阅读graphchecker的readme。给每一个系统上，adhoc coordiaont check都加上我们的annotation。并编号，然后去check他们。…最终我们的目的是，四个system。我们的graphchecker创建四个对应分支。这四个分支代码主体都是一样的。只是每个system可能有一些小适配，workaround。…总之每个系统上我们就要检查若干adhoc coordination。跑出他们的.smt。如果这个点包含我们已有的bug。那应该是.smt跑通。然后你最终跑完这4个system上所有adhoc check。

The 2026-10-04 night goal (HDFS, the current system):

> 跑通hdfs上的所有adhoc check点位。readme里有句话说的不对。我们并不是看small change。这个chagne是系统地探索符号分支，fault。闭包不断演进。最终融合到.smt里。代码可能现在有点臃肿。在你跑通hdfs的同时，你也要删除冗余，不用的代码。并重构非常ugly的代码。最终hdfs所有的点都跑通。能找到新bug最好，找不到也没关系。合理利用10个server并行提升开发速度。

The 2026-10-05 goal (HDFS, the current one), its target and acceptance (verbatim):

> 跑通 HDFS 上全部 46 个 case：36 个 study 检查点 hdfs-adhoc-NN，加 10 个已知 bug 的 named case。完成标准： 1. 每个 case
> 都导出 final/candidate.smt2， - SAT：CONFIRM 已确认，至少移动了一个根，polarityDecides 为真，并做了 native reproduction；
> - UNSAT：exploration 正常到达 FIXED_POINT，并且单独用 z3 重解该文件得到 unsat。 被预算截断（EXPLORATION_CUT）、自相矛盾
> 算 RUN_DEFECT，要修，不能算完成。 2. 10 个已知 bug 全部 PASS，且机制符合 mandate … cone.py 不带任何豁免也要通过。
> 3. 每个 .smt 都人工对照 HDFS 代码核对因果链、符号变量和符号传播 … 每个 SAT 的因果链、每个 UNSAT 的一行解读，写进
> docs/STATUS.md。 4. 最终每个 case … 各跑一遍，结果合并到 main。只有 owner 明确要求时才 push。 找到新 bug 最好，找不到也可以
> 接受，前提是 .smt 正确。

(Exclusive runs were dropped by the owner the same day: "我们不必强行要求独占。一定要最大化10个集群的使用。我们的核心目标是46个
adhoc check先跑通出有正确因果链的.smt".)

In short:
- Four systems, one at a time: HDFS (now), then Solr, HBase, ZooKeeper. One GraphChecker branch per system
  (`system/<sys>`): one engine body, small per-system adapters and workarounds.
- Every selected point is marked `@CausynthExceptionTarget("<sys>-adhoc-NN")` in its tree and checked with its cluster
  test; every check ends with an exported `.smt` that is right (SAT confirmed, or UNSAT at the fixed point); every known
  bug passes; no new bug is an acceptable outcome.
- Delete redundant and unused code, refactor very ugly code, along the way. Use all ten lifts.
- The method is systematic exploration (symbolic branches, faults, an evolving closure, everything fused into one
  `.smt`), never "a small change" (README fixed).

## 2. GraphChecker branches (repo `~/GraphChecker`, remote `origin` = github)

`system/hdfs` is the newest engine body; pushed at this handover (the owner asked). Every in-flight branch below has a
WIP or finished commit and its worktree; merge them in TODO §1's order.

| branch | head | worktree | state |
| --- | --- | --- | --- |
| `system/hdfs` | `176acc689` + this handover's docs | `/bigtemp/vnr3ne/wt/gc-hdfs` (full checkout) | **The HDFS body.** Built, unit- and shell-tested. Merged 2026-10-05/06: clock placement (bd71f7490), claim loop (aaa2befe7), bound mark (d2678f203), round-verify UNBOUND (851131dd6), `tools/lib/worktree-add.sh` (f4a50da3b), the host ledger's one refresher (b7c5dc99d), the 01/17/43 -> 06/38/45 swap (55ffd81f7), confirm-first (adffd6072), (b2) arm-rests-on with the handoff rule (18f853467), the guard decider (b650a0f6d), the shim's codec entry points (176acc689). |
| `hdfs-export-weave` | `073e4a3af` | `/bigtemp/vnr3ne/wt/gc-hdfs-export-weave` | A1. Every static export site woven; a witness ends exploration only when its own chain is closed (chain mode, `WITNESS_CHAIN_OPEN`); a SAT judged on its claimed path, an UNSAT on every path (`unboundOffWitness`, `UNSAT_CHAIN_OPEN`; cone.py/report.py aligned). Units + shell pass; AW4-12/AW5-12 SAT unbound 0; AW4-11741 PASS (all 11 handoffs bound, the key id by `message_family__19__975186a47596`); AW5-17897 PASS. Owed: a second 11741 on `~/gc-run/aw5`, then merge. |
| `hdfs-frontier-depth` | `b3b6885a4` | `/bigtemp/vnr3ne/wt/gc-hdfs-frontier-depth` | D1. Set-valued arm keys; `AB_STAGES=EXPLORE.drift`; the owed-path bound (paths beyond it deferred, never dropped). 05 06 08 09 FIXED_POINT `bounded: null`, 17897 PASS (snapshot `fd2` = 34e9d0cae). Owed: 11741 x2 with `CASE_TIMEOUT_SECONDS=10800` (FD3/FD3b stopped unfinished). |
| `hdfs-solver-fallback` | `a0bacf303` | `/bigtemp/vnr3ne/wt/gc-hdfs-solver-fallback` | D1. A host solver killed at its memory hold is placed by its measured peak through the ledger, or fails by name at once. Units + shell pass; never run live. |
| `hdfs-container-writers` | `4babe9a51` | `/bigtemp/vnr3ne/wt/gc-hdfs-container-writers` (sparse) | D1. The prefix span (a loop-body root's enclosing entry opens the region for the method prefix) + review fixes; system/hdfs b650a0f6d merged. Canaries 19 21 28 29 11741 passed on an older base; 11 does not converge (CW5: 1267 asks vs 47): needs rule 1 (TODO §1.7; prototype `/bigtemp/vnr3ne/handover/2026-10-06/rule1-demanded-sites.patch`). |
| `hdfs-time-model` | `49f502302` | `/bigtemp/vnr3ne/wt/gc-hdfs-time-model` | A2. Reviewed; review fixes in (the pre-window rule, ScheduleLog the single owner of the cap, the named pre-contract refusal, docs, tests); system/hdfs 176acc689 merged. tm16 gate (5ce36a51e): no 120 s stand; 11741 PASS CLOCK_SKEW 3004 s; 17897, bug1, 17960 PASS. Owed: one live check on its head; 11741 replays median 258 s (TODO §4). |
| `hdfs-ipc-handoff-name` | `f92460764` | `/bigtemp/vnr3ne/wt/gc-hdfs-ipc-handoff` | A2, stacked on the time model: a hand-off of a received call to the handler queue named by the call's request identity (the server twin of r5's per-verb naming); needs the r6 trees. Code done; build/tests not rerun after its last rebase. |
| `hdfs-codec-capture` | (head) | `/bigtemp/vnr3ne/wt/gc-hdfs-codec-capture` | agent C, on `hdfs-int` fafd89f40 + `hdfs-shim-dt-door` 5888aec74: the IPC and DataTransfer doors walk the protobuf message, the engine's plumbing never state; needs the r6 trees (study-r6 7e81b3a588c); gates owed (TODO §1.6). |
| `hdfs-compose-perf-wip` | `8509b431d` | `/bigtemp/vnr3ne/wt/a1-measure` | A1's measurement code (17897 COMPOSE: two z3 runs per sat ask, 16-56 s asks). Not for merge. |
| `hdfs-refactor-compose` | `ac2f58490` | `/bigtemp/vnr3ne/wt/gc-hdfs-refactor-compose` | Behaviour-preserving COMPOSE refactor, steps 1-4 gated identical; step 5 not started; system/hdfs not merged into it since 2026-10-05 (TODO §6). |
| `hdfs-clock-replay` | `22520bf02` | none | C1 (keyed clock replay), parked; delete when the time model merges. |
| `hdfs-construction-only-values` | `ca50b8319` | | parked since 10-04 (needs an 11741 chain check). |
| merged this session, deletable | | | `hdfs-clock-place`, `hdfs-claim-loop`, `hdfs-bound-scope`, `hdfs-swap-clock`, `hdfs-confirm-first`, `hdfs-arm-rests-on`, `hdfs-handoff-rule`, `hdfs-decider-open`, `hdfs-shim-codec-entries`, `hdfs-native-plant`, `hdfs-wire-decl`, `hdfs-request-door`, `hdfs-window-counts`, `hdfs-sorted-listings`, `hdfs-anchored-index`, `hdfs-compose-cost`, `hdfs-seed-speed`, `hdfs-draw-sites2`, `hdfs-address-shared` (remove their worktrees first: `git worktree list`). |
| `main` | `fe3a5f1a0` | `~/GraphChecker` | the 2026-10-03 handover body (V25 14/14). `system/solr`, `system/hbase`, `system/zookeeper` = `main`. |
| `solr-bug-reindex` | `12283e3f1` | `.claude/worktrees/agent-a6cdfa854234df67e` | Solr #04 + Solr replay fidelity; SBR26 13/14 (solr-18413 regressed). Parked for the Solr turn. |
| `hb-schedule` + `hb-sync` | `1fb4a475a`, `53f16e8b6` | `.claude/worktrees/agent-aea16c87adafb5d81` | one per-session happens-before relation; reviewed; for the ZooKeeper turn. |
| `hbase-startup` | `3afb27f13` | `/bigtemp/vnr3ne/wt/gc-hbase-startup` | HBase #14; blocked on two design questions (TODO HBase). |
| `wire-codec-p1` | `3e9cb3182` | `.claude/worktrees/wire-codec-p1` | WIRE-CODEC, the only home of that feature. Resume only for a system that needs it. |
| `study` | `b9da03fc1` | `/bigtemp/vnr3ne/wt/gc-study` | `study.txt` and `selection.txt` (HDFS-01/17/43 swapped out for 06/38/45, HDFS-32 for 05); the tables are also in `docs/checks/`. |

How the system branches relate: the engine body moves on `system/hdfs` only; when HDFS is done it goes to `main`, and
`main` is merged into `system/solr`, `system/hbase`, `system/zookeeper`, each then adding only its adapter, markers
and cases. The HBase tree must drop a codec argument before any HBase run on the new body (§3).

## 3. System trees (the code under test)

| tree (worktree) | branch, head | state, used by |
| --- | --- | --- |
| `/bigtemp/vnr3ne/wt/hadoop-hdfs-study-r3` | `gc/hdfs-study-r3` `d03c1f9134a` | superseded by r4 (R4A, 2026-10-05); kept only for the runs that name it, never touched again. = `gc/hdfs-study-next` + `gc/hdfs-study-startup`. Maven repo `/bigtemp/vnr3ne/m2/hdfs-study-next`. |
| `/bigtemp/vnr3ne/wt/hadoop-hdfs-study-r6`, `/bigtemp/vnr3ne/wt/hadoop-hdfs-11741-r6` | `gc/hdfs-study-r6` `1c30e21f488`, `gc/hdfs-11741-r6` `6c86fca9a2b` (on r5) | **Committed, not built.** r5 + A2's IPC hand-off hook (`Server#internalQueueCall` in `CausynthMessagePropagation.handingOff/handedOff`: 5e01e556b33 / 5a139fed92a) + A4's three door calls (`Server#setupResponse` -> `outboundResponse(..., rv)`; `received(msg)` after the client's and the server's parse, in ProtobufRpcEngine2 and v1). The study-r6 worktree holds r5's copied outputs and one hand-compiled `Server.class`: rebuild both properly before use (OPERATIONS §1), then switch every `case.sh` in one commit (TODO §1.5). |
| `/bigtemp/vnr3ne/wt/hadoop-hdfs-study-r5` | `gc/hdfs-study-r5` (on r4) | **every HDFS case but 11741** (`experiments/hadoop/*/case.sh repo=`). = r4 + the IPC request starts at the RPC engine's invoke point (`ProtobufRpcEngine2`/`ProtobufRpcEngine` `Invoker#invoke`: `CausynthMessagePropagation.requestStarting`/`requestEnded`, `Client#causynthAttempt`; `Client#sendRpcRequest`'s hand `endInbound()` deleted, so its loop sites are `#u53`/`#u58`). Maven repo `/bigtemp/vnr3ne/m2/hdfs-study-r5` (the GraphChecker jar of `hdfs-request-door` installed in it); every case's workload run once natively there before its first run (its surefire report is the classpath). |
| `/bigtemp/vnr3ne/wt/hadoop-hdfs-study-r4` | `gc/hdfs-study-r4` `42f029cc568` | superseded by r5; kept for the runs that name it, never rebuilt. = r3 (the 49 study markers, MiniJournalCluster hooks, node-startup brackets, the startup window, weak adapter registries, the NN heartbeat tick, the IPC door naming its verb, the NN's `registerDatanode` write lock as the startup step) + the IPC handler opens a call's exchange before `doAs` (`Server.Handler#work`, `Call#causynthEnter/Exit`, `RpcCall#run` back to upstream) + DataXceiver's redundant hand `endInbound()` removed. Built (Maven repo `/bigtemp/vnr3ne/m2/hdfs-study-r4`, the GraphChecker jar of 62308852c installed in it: the copied one lacked `startupStep`), every HDFS case's workload run once natively (its surefire report is what a case's classpath reads); validated in R4A (`/bigtemp/vnr3ne/gc-out/hdfs-r4`). |
| `/bigtemp/vnr3ne/wt/hadoop-hdfs-11741-verb` | `gc/hdfs-11741-verb` `0d24b5f626b` | superseded by 11741-r4; kept only for the runs that name it. Maven repo `/bigtemp/vnr3ne/m2/hdfs-11741-verb`. |
| `/bigtemp/vnr3ne/wt/hadoop-hdfs-11741-r5` | `gc/hdfs-11741-r5` (on 11741-r4) | **hdfs-11741**: 11741-r4 + the same request start. Maven repo `/bigtemp/vnr3ne/m2/hdfs-11741-r5`. |
| `/bigtemp/vnr3ne/wt/hadoop-hdfs-11741-r4` | `gc/hdfs-11741-r4` `a703b618d34` | superseded by 11741-r5; never rebuilt. 11741-verb + the same handler change. Built, workload passes natively; Maven repo `/bigtemp/vnr3ne/m2/hdfs-11741-r4`; validated in R4A. |
| `hadoop-hdfs-study-next`, `-study-startup`, `-study`, `-bugs`, `-dtx`, `-dtx-w6`, `-11741-w6` | | bases or older trees; `main`'s cases run `hadoop-hdfs-dtx` (`gc/hdfs-unified-dtx`). The HDFS-group ones can go once r4 is in. |
| `/bigtemp/vnr3ne/wt/lucene-solr-storing` | `gc/solr-unified-storing` `04f8489` | solr-18406, solr-18413 (main). Also `lucene-solr-bugs` (`gc/solr-bugs` `f65aaf7`, the Solr bug_study cases), `lucene-solr-storing2` (`40b7659`); clones `~/lucene-solr-8_11`, `~/lucene-solr-unified`. The Solr trees carry the upstream ZkStateReader-race workaround (OPERATIONS §8). Study markers not added yet. `MessageDoors.consumed` installs an envelope without its message key, so a consumed Overseer item's concrete elements stay unpaired (STATUS open defect 50). |
| `/bigtemp/vnr3ne/wt/zookeeper-unified`, `zookeeper-hb` | `gc/zk-unified` `8f18cf3a4`, `gc/zk-unified-hb` `47ddc8b36` | the zk-bugs cases (main); `-hb` adds the RESPONSE door for `hb-schedule`. Maven repos `/bigtemp/vnr3ne/m2/zookeeper`, `/bigtemp/vnr3ne/m2/zookeeper-hb`. Its only remote is apache: never push. Study markers not added yet. |
| `/bigtemp/vnr3ne/wt/hbase-unified` | `gc/hbase-unified` `1051825287` | HBase cases (`hbase-startup`). **Must change before any HBase run on the new body**: `CausynthRpc.java:61-62` passes `call.param` to a payload door the WIRE-CODEC deletion removed; drop `, call.param` and rebuild hbase-client. Study markers not added yet. |

VM images: `/bigtemp/vnr3ne/vm-hg5/j2sdk-image` serves `system/hdfs` (sources = branch `hdfs-vm-hg5` 742f13363, merged;
`SOURCE.txt` beside it); `vm-model-guards2` serves `main`; `vm-size-source` served HG4; `vm-hdfs-scope-container`,
`vm-hdfs-scope-rows`, `vm-model-guards`, `vm-streams` are superseded. No VM change was made this session. The VM's
dead natives (VM.md §8: `getPathCondition`, `trackContainerExpression`, `getShared*Versions`,
`getConcolicRegionSummary`, the `armShared*`/`confirmShared*` refusals) and `exportLeaf`/`mintLeaf` (WIRE-CODEC only)
can go in the next VM build.

Snapshots in `~/gc-run/`: `hg7` (272afdef2) is the last round's body; agents' `as1`, `hcl1`, `hds9`-`hds14`, `whf1`
and every older one (`hcs-*`, `hdv*`, `hg3`, `hg4`, `hg5*`, `hoa*`, `hsc*`, `hscope1`, `hsr1`, `hssp1`, `iof*`) can go
(`tools/rounds/snapshot-gc.sh` refuses one in use).

## 4. Rounds and the state of each check

Outputs `/bigtemp/vnr3ne/gc-out/hdfs-study/accept-<round>-<n>/` (`sweep-<round>-cases.tsv` maps n to the case; a
rerun's suffix names its case, `HG9L-11`); agents' runs under `/bigtemp/vnr3ne/gc-out/<branch>/`.

| round | body | result |
| --- | --- | --- |
| HG7, HG7R, HG7N, HG7D, HG8A | `272afdef2`, `84f53669b`, `4d76294a3` | the 2026-10-05 day's rounds (STATE of 2026-10-05; git history) |
| HG8E, HG8F, HG8W, HG8Z | 2026-10-05 bodies up to `2a5bec483` | HG8F: the 10 named PASS; the clock family stopped at 80+ give-ups; 05 UNSAT (HG8W), 52 UNSAT (HG8Z) on older bodies |
| HG9 | `aaa2befe7` (clock placement + claim loop), 35 non-clock cases, 2 heads/host, 90-min budget | 10 SAT; 07 14 15 16 19 20 27 28 29 30 31 39 40 48 UNSAT at FIXED_POINT (07: UNBOUND 6, 14: UNBOUND 3); 05 11 12 26 33 37 cut by the budget; 08 09 timed out |
| HG9B | the same, 3 h budget | named 9 PASS (11741: two unbound key-id handoffs); 49 50 UNSAT |
| HG9L-05/11/12/26/33/37 | the same, 3 h budget | 11 26 33 37 UNSAT at FIXED_POINT; 05 FIXED_POINT but 85 bounded rows; 12 SAT confirmed, reproduced 4/10, 1 unbound (txid) |
| SW1, SW1L-45 | `a147c2448` (swap rows) | 38 UNSAT (13 symbols); 45 UNSAT NO-SYMBOL; 06 UNSAT but 51 bounded rows |
| HG10V | `b650a0f6d` ((b2) + decider) | 17897 PASS in 594 s; stopped at the handover |
| agents' rounds (own `GC_OUT`) | | TM12-TM16 (time model: `hdfs-time-model/probe/runs.txt`), CL3 (claim loop), AR1-AR3 ((b2)), AW4-AW5 (export weave), DO1-DO2 (decider), FD1-FD3 (frontier depth), CW3-CW5 (container writers), NP7 (native plant), WD1-WD3 (wire flows) |

Per check: [../checks/README.md](../checks/README.md) (state per row), how each is checked: [CHECKING.md](CHECKING.md).
Summary (46 HDFS cases, 2026-10-06 handover):
- known bugs: 9/10 PASS by mandate on the merged body (HG9B); 11741 PASS with a clean cone on (b2) (AR3, merged) and on
  the time model (TM16), so 10/10 have passed; the final round re-confirms.
- study checks: done 20 -- 11 15 16 19 20 26 27 29 30 33 37 38 40 49 50 UNSAT with symbols, 28 31 45 48 UNSAT over a
  chain constant in the window (reasons in their rows), 10 SAT; fixed on a branch, owed a merge and the final round, 6
  -- 12 (export weave), 14 ((b2), merged), 05 06 08 09 (frontier depth); in work 2 -- 07 (codec capture), 39 (its bug's
  arm unreachable in replay); the time-model family 8 -- 21 22 23 24 25 34 35 52 (time model, hand-off naming, then the
  three quick workarounds of TODO §2: quiesce before the window, no `du`/`df` forks, IBRs at once).
- swapped (owner 2026-10-05): 32 for 05; 01 17 43 for 06 38 45. New bugs: none.

Snapshots in `~/gc-run/` (each frozen; `tools/rounds/snapshot-gc.sh` removes one no process names): `hg9` (HG9's
body), `sw1` (the swap rows), `aw5`/`aw4` (export weave), `ar3` ((b2)), `fd2` (frontier depth), `cw3` (container
writers), `tm16` (time model), `a4base` (A4's base).

## 5. Where the analyses and evidence live

- `docs/checks/` (in the repo): the selection, the per-system point tables, the verified bugs.
- `/bigtemp/vnr3ne/analysis/study-2026-10-04/`: `AGENT-RULES.md` (every coding agent's rules), the briefs of this
  session's packages (`brief-*.md`; the open ones: `brief-refactor-compose.md`, `brief-planned-shape.md` (its third
  package), `brief-cleanup-1.md` (phase-2 items)), `cleanup-audit/` (the dead-code audit's tables).
- `/bigtemp/vnr3ne/ab/`: offline gates (`hdfs-decisive-verdicts/finish/`, `hdfs-refactor-compose/` with `cost-gate.sh`
  and 07's COMPOSE samples `c07/`, `cleanup-*`).
- `/bigtemp/vnr3ne/gc-out/diag-11741/`: the 11741 regression's diagnosis run (292 MB; delete once 11741 passes).
- `/bigtemp/vnr3ne/gc-out/hdfs-seed-speed/`: SEED profiling (strace, jstack scripts).
- `/bigtemp/vnr3ne/specs/`: `WIRE-CODEC-proposal.md`, `R1-ROOTS-proposal.md`, `R3-REFCONT-proposal.md` (cited by code
  comments and the design docs).
- `/bigtemp/vnr3ne/handover/`: bundles of deleted branches and old WIP patches.
- `/bigtemp/vnr3ne/handover/2026-10-06/`: D1's rule-1 prototype patch and the 2026-10-05/06 session's scratch scripts
  and notes (`scratchpad/`: HG9 verify output, legends of 12 and 14, analysis scripts).
- `/bigtemp/vnr3ne/analysis/study-2026-10-05/`: that session's briefs and per-case `.smt` readings (`smt-checks.md`,
  `legends/`).
- Agents' evidence: `/bigtemp/vnr3ne/gc-out/hdfs-time-model/` (probe/runs.txt, stalls.py, around.py, untaken.py),
  `hdfs-arm-rests-on/` (AR1/AR3/AW4/AW5), `hdfs-decider-open/` (DO1/DO2), `hdfs-frontier-depth/` (FD*), `hdfs-container-
  writers/` (CW*); offline gates `/bigtemp/vnr3ne/ab/hdfs-refactor-compose/` (gate2.sh, armC-*), `/bigtemp/vnr3ne/ab/
  a1-tmp/` (planner46.py), `/bigtemp/vnr3ne/ab/fd-owed-gate2`, `fd-direct`, `fd-drift*`.
- `~/bug_study/*.txt`: the bug descriptions.
