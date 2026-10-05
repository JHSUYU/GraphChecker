# State at the handover of 2026-10-05 morning

The owner stopped the lead and every agent ("请你停止你手头的所有任务，包括所有子agent的task…我要让别的coding agent读了可以直接接手").
Nothing runs on any lift: round HG7 was stopped after 7 study verdicts, and each coding agent stopped and committed
its WIP. Read this file, then [TODO.md](TODO.md), [RULES.md](RULES.md), [AGENTS.md](AGENTS.md) and
[OPERATIONS.md](OPERATIONS.md). The design is in [../design/](../design/README.md) (performance and the cluster:
[../design/PERFORMANCE.md](../design/PERFORMANCE.md)); every check per system with its live state is in
[../checks/README.md](../checks/README.md); what is done / partial / missing per requirement is in
[../STATUS.md](../STATUS.md).

## 1. The goals (verbatim) and what they mean

The 2026-10-04 goal (the four systems):

> 请你阅读graphchecker的source code和vm代码。先了解这个Tool在处理的adhoc coordinaiton。以及我们的处理方式。然后阅读graphchecker远端study分支上的study.txt。里面记录了4个system的adhoc coordianotin位置，以及他们对应的cluster based unit test。同时，~/bug_study下是一些可能是adhoc coordianot有关的bug。请你仔细阅读graphchecker的readme。给每一个系统上，adhoc coordiaont check都加上我们的annotation。并编号，然后去check他们。…最终我们的目的是，四个system。我们的graphchecker创建四个对应分支。这四个分支代码主体都是一样的。只是每个system可能有一些小适配，workaround。…总之每个系统上我们就要检查若干adhoc coordination。跑出他们的.smt。如果这个点包含我们已有的bug。那应该是.smt跑通。然后你最终跑完这4个system上所有adhoc check。

The 2026-10-04 night goal (HDFS, the current system):

> 跑通hdfs上的所有adhoc check点位。readme里有句话说的不对。我们并不是看small change。这个chagne是系统地探索符号分支，fault。闭包不断演进。最终融合到.smt里。代码可能现在有点臃肿。在你跑通hdfs的同时，你也要删除冗余，不用的代码。并重构非常ugly的代码。最终hdfs所有的点都跑通。能找到新bug最好，找不到也没关系。合理利用10个server并行提升开发速度。

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

`system/hdfs` is the newest engine body. It is **not pushed** since `43ba5d565` (the 2026-10-04 handover); push only
when the owner asks.

| branch | head | worktree | state |
| --- | --- | --- | --- |
| `system/hdfs` | `e627173c4` + this docs commit | `/bigtemp/vnr3ne/wt/gc-hdfs` | **The HDFS body.** Built, unit- and shell-tested. Merged on 2026-10-05 (day): `hdfs-compose-cost` (4d76294a3), `hdfs-sorted-listings` (5b389ef42: directory listings sorted in both passes), the reserve owing REPRODUCE its own bound (730c93308), `hdfs-anchored-index` (every HDFS case on the r4 trees, e627173c4); docs/handover/PARALLEL.md and the round tools' NO-SYMBOL / STALLS-REGRESSION flags (fcf123dbc). |
| `hdfs-compose-cost` | merged (4d76294a3) | | deletable |
| `hdfs-refactor-compose` | `99c7d829d` | `/bigtemp/vnr3ne/wt/gc-hdfs-refactor-compose` | Behaviour-preserving refactor, steps 1-4 done and gated (COMPOSE outputs identical on V25, HG5A, HG4, 11741; `solverRuns`/`unsatCore` excluded as run-to-run noise, `stable.py`): ClaimPolicy.read 213 -> 12 lines, stateFamilies 294 -> 25, producerBody 162 -> 15, ContainerSmtCodec's switch ladders -> one rule table. Not merged; system/hdfs not merged into it; step 5 (Composer.compose/run, the SmtLowering split) not started. Brief `/bigtemp/vnr3ne/analysis/study-2026-10-04/brief-refactor-compose.md`. |
| `hdfs-anchored-index` | merged (e627173c4) | | deletable |
| `hdfs-sorted-listings` | merged (5b389ef42) | `/bigtemp/vnr3ne/wt/gc-hdfs-sorted-listings` | deletable |
| `hdfs-container-writers` | (D1, coding) | `/bigtemp/vnr3ne/wt/gc-hdfs-container-writers` | Design approved: the writers of a demanded container planned in SEED's DemandWalk on any logical node of the reader's JVM (the owning object decides, `holdsOthersOnly` corrected for late-started logs), the same rule in ClosurePlanner, `orphansAFold` by call unit (a fold before a loop-body root's loop opens the region at the method entry). For 11 31 (28 29 to confirm). Review before merge. |
| `hdfs-handoff-rule` | `794013bf3` (A3) | | One handoff rule at every depth (ComposedFamilies#handedOn calls Composer#handoffRead): 11741's witness path binds the key id by its SASL family; COMPOSE/CONFIRM byte-identical on 8 named corpora. In review. Paths through an uninstrumented balancer move (executePendingMove@1) still HELD: a closure fix owed (no cone.py exemption). |
| r5 trees + identity amplifier | (A3, coding) | | Approved: a request door first ends the exchange its thread stands in and is counted per verb in hand (`MessageDoors.requestStarting` at the RPC engine's invoke point, new tree branches gc/hdfs-study-r5, gc/hdfs-11741-r5); an extra RPC (retry, heartbeat) no longer renames every later request (hdfs-adhoc-52's give-up cascade). Review before merge. |
| `hdfs-seed-speed` | merged (093c8918b) | | deletable (its worktree became `gc-hdfs-native-plant`) |
| `hdfs-native-plant` | this row's commit | `/bigtemp/vnr3ne/wt/gc-hdfs-native-plant` | REPRODUCE plants CONFIRM's world (`ConfirmMain.Witness` shared by CONFIRM and `--plant`): FAULT markers, tree HOOK roots, CONFIRM's ORDER rows held by `Confirmation` at `Identity`'s frame hooks, TARGET rows; each run's answer states every row applied (or UNHELD / HOLDING / NOT_REACHED); a native run gets at least `reproduce_min_s` (300). Round NP1/NP2 (`/bigtemp/vnr3ne/gc-out/hdfs-native-plant/`): slowdisk-zero 10/10 at the anchor (3 ORDER rows held, 2 of them waited), 17897 10/10 (unchanged), 17960 10/10 (NP2; HOOK row written at the restart's mint occurrence; NP1's 24 s bound cut all ten runs). Not yet: CLOCK rows (after the time model's `Clocks` merges), CONFIG roots (the recording weave has neither the configuration-read nor the getter-call mint; no current claim moves one). |
| `hdfs-time-model` | (A2, coding) | `/bigtemp/vnr3ne/wt/gc-hdfs-time-model` | Design approved 2026-10-05: application clock reads in a replay follow the recording's timeline re-anchored at every move of the order (v = max(last, min(hi, lo + elapsed))), a CLOCK root's skew on top, no keyed reads. Probes of 01 17 21 22 23 25 34 35 43 52, then a review agent. |
| `hdfs-draw-sites2` | `2d84363cd` | `/bigtemp/vnr3ne/wt/gc-hdfs-draw-sites` | HG6, merged (825f190a7) via hdfs-address-shared; its later commits only merge system/hdfs into it. Deletable. |
| `hdfs-clock-replay` | `22520bf02` | none | C1 (keyed clock replay), parked; its commit message holds the C1 findings the time model starts from. |
| `hdfs-construction-only-values` | `ca50b8319` | | parked since 10-04 (needs an 11741 chain check). |
| `main` | `fe3a5f1a0` | `~/GraphChecker` | the 2026-10-03 handover body (V25 14/14). `system/solr`, `system/hbase`, `system/zookeeper` = `main`. |
| `solr-bug-reindex` | `12283e3f1` | `.claude/worktrees/agent-a6cdfa854234df67e` | Solr #04 + Solr replay fidelity; SBR26 13/14 (solr-18413 regressed). Parked for the Solr turn. |
| `hb-schedule` + `hb-sync` | `1fb4a475a`, `53f16e8b6` | `.claude/worktrees/agent-aea16c87adafb5d81` | one per-session happens-before relation; reviewed; for the ZooKeeper turn. |
| `hbase-startup` | `3afb27f13` | `/bigtemp/vnr3ne/wt/gc-hbase-startup` | HBase #14; blocked on two design questions (TODO HBase). |
| `wire-codec-p1` | `3e9cb3182` | `.claude/worktrees/wire-codec-p1` | WIRE-CODEC, now the only home of that feature (its runtime was deleted from the system body as unreachable on every case). Resume only for a system that needs it. |
| `study` | `8d9621e7a` | `/bigtemp/vnr3ne/wt/gc-study` | `study.txt` and `selection.txt` (pushed); the tables are also in `docs/checks/`. |
| merged, deletable | | | every branch `git branch --merged system/hdfs` lists (about 60: the `hdfs-*` feature branches, `main-*`, `hg4`, `hg5`, `vm-*`, `system-zookeeper`, ...), and the superseded `fix-no-root`, `fix-hdfs-seed-stalls`, `recording-stall-guard`, `replay-heap-bound*`, `state-pairing`, `system-hbase`, `hb-base`, `perf-vm-readout`, `vm-ref-compare`, `main-v22`, `worktree-agent-a49c8bf5715a00c40` (bundles of older ones in `/bigtemp/vnr3ne/handover/`). Remove their worktrees first (`git worktree list`). |

How the system branches relate: the engine body moves on `system/hdfs` only; when HDFS is done it goes to `main`, and
`main` is merged into `system/solr`, `system/hbase`, `system/zookeeper`, each then adding only its adapter, markers
and cases. Since the WIRE-CODEC deletion, `wire-codec-p1` no longer merges cleanly into the body, and the HBase tree
must drop a codec argument before any HBase run on the new body (§3).

## 3. System trees (the code under test)

| tree (worktree) | branch, head | state, used by |
| --- | --- | --- |
| `/bigtemp/vnr3ne/wt/hadoop-hdfs-study-r3` | `gc/hdfs-study-r3` `d03c1f9134a` | superseded by r4 (R4A, 2026-10-05); kept only for the runs that name it, never touched again. = `gc/hdfs-study-next` + `gc/hdfs-study-startup`. Maven repo `/bigtemp/vnr3ne/m2/hdfs-study-next`. |
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

Outputs `/bigtemp/vnr3ne/gc-out/hdfs-study/accept-<round>-<n>/` (`sweep-<round>-cases.tsv` maps n to the case);
agents' runs under `/bigtemp/vnr3ne/gc-out/<branch>/`.

| round | body | result |
| --- | --- | --- |
| HG4 | `2680e7f63`, image vm-size-source | named 8 PASS; its "23 UNSAT" included explorations cut by the budget (07/08/09 at ~4940 s) and a silently wrong allKeys read in 11741 |
| HG5A | `e76f6b4a8` (the HG5 body), 10-04 23:40 - 10-05 02:40, PRUNE=1 | the baseline the lead diagnosed from: named 9 PASS, 11741 a regression (cause: an unplanned key-update occurrence); study 14 UNSAT at the fixed point, 2 SAT; 7 budget-cut; 7 RUN_DEFECT with causes; 7 stopped (time-model class) |
| HG7 | `272afdef2` (every branch merged), 10-05 08:45 - 09:20, PRUNE=0 | **stopped by the owner** after 7 study verdicts, all checked (FIXED_POINT or WITNESSED, z3 re-solve agrees): 10 SAT, 12 SAT, 11 15 16 19 20 UNSAT. Stopped by the lead: 01, 21, 25 (80+ seed give-ups). Everything else unfinished |
| agents' rounds | | RIH1 (bug1/2/3 PASS, unexempted cone), MCH1/MCH2 (measured charges), WHF1 (wire-half: 07 self-contradictions 177 -> 0; bug1/bug2/17897/pathA PASS), HCL1 (E1: 16 UNSAT, 17960 PASS, 20 UNSAT), PS1-PS3 (planned shape: 11741 witness confirmed, allKeys complete 100/100; bug1, 17897, 17960 PASS), HR1 (head reserve; 07's COMPOSE timeout), DW1-DW5a (HG6 probes), AS0-AS2 (address-shared) |
| HG7R | snapshot `hg7r` = 84f53669b (HG7's code), 10-05 day, PRUNE=0 | 15 reruns: 27 28 29 30 31 33 39 40 48 49 50 UNSAT at FIXED_POINT (28 29 31 NO-SYMBOL); 24 26 37 52 stopped at 80+ give-ups (24/26/37: listing order, fixed) |
| HG7N | `hg7r` | the 10 named cases: all PASS by mandate, cone clean (17960, 11741, slowdisk-zero without a native reproduction: only fault markers are planted natively) |
| HG7D, HG8A | `hg7r`; `hg8a` = 4d76294a3 | QJM with a 3 h budget: 08 09 07 UNSAT at FIXED_POINT in 29-44 min |
| SL1-SL3 | `sl1` = hdfs-sorted-listings | 24/26/37 give-ups 5/12/13 (were 84/89/80) but cut by the budget (reserve fixed); canaries unchanged; the time-model class on listings alone: 25 34 down, 01 17 21 35 still 80+ |
| R4A (A3) | r4 trees | 14 UNSAT at FIXED_POINT; bug1, 17897, 17960 PASS; 11741 confirmed CLOCK_SKEW |
| HG8B | `hg8b` = 50b64875f | 24 26 37 with a 3 h budget (running at this commit) |

Per check: [../checks/README.md](../checks/README.md). Summary (46 HDFS cases, 2026-10-05 day):
- known bugs: 10/10 PASS by mandate on the current body (HG7N); on `hdfs-native-plant` 17960 (its configuration hook
  root) and slowdisk-zero (its re-pairing, held as ORDER rows) reproduce natively 10/10, 11741 (clock) still owed
  until the time model merges; 11741's key-id binding still timing-dependent (A3);
- study: 18 right-shaped verdicts (10 12 SAT; 07 08 09 14 15 16 19 20 27 30 33 39 40 48 49 50 UNSAT at the fixed
  point with symbols); 11 28 29 31 UNSAT with no symbol (container reads pinned: D1); 24 26 37 rerunning (HG8B); 52 and
  32 open; 01 17 21 22 23 25 34 35 43 the time-model class (A2);
- new bugs: none.

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
- `~/bug_study/*.txt`: the bug descriptions.
