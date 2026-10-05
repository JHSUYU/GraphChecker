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
| `system/hdfs` | this handover's docs commit, on `2e89a9e69` | `/bigtemp/vnr3ne/wt/gc-hdfs` | **The HDFS body.** Built, unit-tested (350), shell-tested. Since the 10-04 handover it merged: `hdfs-request-in-hand`, `hdfs-measured-charges`, `hdfs-decisive-verdicts` (reviewed), `hdfs-wire-half`, `hdfs-closure` (E1), `hdfs-cleanup-1`, `hdfs-cleanup-2` (head reserve, WIRE-CODEC deleted), `hdfs-address-shared` with HG6 (`hdfs-draw-sites2` 825f190a7, reviewed); plus lead fixes (FREEZE digest d8d26347e, array identity d027740d2, README, RULES). Last complete round: none on this body (HG7 stopped, §4). |
| `hdfs-compose-cost` | `df4cf40f8` (WIP, builds, tests pass) | `/bigtemp/vnr3ne/wt/gc-hdfs-compose-cost` | 07's COMPOSE timeout fixed: the self-check's quadratic `indexOf` over the 26 MB body (a refuted-claim flag per command from its last 64 chars), worker dirs read 8 at a time, COMPOSE progress lines; 116 s offline on HR1's corpus (was > 17 min). **Not gated, no docs.** Next: `/bigtemp/vnr3ne/ab/hdfs-refactor-compose/cost-gate.sh` with the branch jar against system/hdfs, docs, merge. |
| `hdfs-refactor-compose` | `99c7d829d` | `/bigtemp/vnr3ne/wt/gc-hdfs-refactor-compose` | Behaviour-preserving refactor, steps 1-4 done and gated (COMPOSE outputs identical on V25, HG5A, HG4, 11741; `solverRuns`/`unsatCore` excluded as run-to-run noise, `stable.py`): ClaimPolicy.read 213 -> 12 lines, stateFamilies 294 -> 25, producerBody 162 -> 15, ContainerSmtCodec's switch ladders -> one rule table. Not merged; system/hdfs not merged into it; step 5 (Composer.compose/run, the SmtLowering split) not started. Brief `/bigtemp/vnr3ne/analysis/study-2026-10-04/brief-refactor-compose.md`. |
| `hdfs-anchored-index` | `b9dd06e31` (docs only) | `/bigtemp/vnr3ne/wt/gc-hdfs-anchored-index` | Option A for hdfs-adhoc-14: the IPC server's handler opens a call's exchange before `doAs`, so a NameNode-handler occurrence stands on its call's anchor (STATUS per-system row, IDENTITY §7.1). The code is in the r4 trees (§3), WIP, **not built, not validated**. |
| `hdfs-seed-speed` | this row's commit | `/bigtemp/vnr3ne/wt/gc-hdfs-seed-speed` | SEED's static pass: `IndexedSourceLocator` (Soot's directory lookup answers from each folder's listing, read once per JVM; a listed name is Soot's own lookup), the pass's JVM on the jar alone (`java.class.path` no longer appended to Soot's classpath), `experiments/hadoop/classpath.py` takes every entry under the reporting checkout from the case's tree (r3 loses study-next's two class dirs). Gate: `offline-ab AB_STAGES=SEED.static` over 12 HDFS cases (HG7/HG7R), identical 12/12 and base~acc same 12/12 (`/bigtemp/vnr3ne/gc-out/hdfs-seed-speed/gate2`); strace of one hdfs-adhoc-19 pass 232K -> 41K file syscalls, failed NFS stats 197K -> 7K; warm pass walls unchanged. Ready to merge. |
| `hdfs-time-model` | `ccbf0f8a0` (empty WIP commit holding the design) | `/bigtemp/vnr3ne/wt/gc-hdfs-time-model` | The start-up/clock family's time model, **design not yet approved, no code** (TODO HDFS §3): the recording stamps every schedule event and STARTUP mark with its clock readings; every application clock read goes through `Clocks` (as C1 did); in a replay the application sees the recording's timeline, never past the stamp of the frontier slot (before the window: the next STARTUP mark) and never backwards; a declared CLOCK root keeps its skew on top; no read is keyed. Evidence: HG6's DW probes (`/bigtemp/vnr3ne/gc-out/hdfs-draw-sites/hg6/runs.txt`) and `hdfs-clock-replay` 22520bf02's findings. |
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
| `/bigtemp/vnr3ne/wt/hadoop-hdfs-study-r3` | `gc/hdfs-study-r3` `d03c1f9134a` | **every HDFS case but 11741** (`experiments/hadoop/*/case.sh repo=`). = `gc/hdfs-study-next` (the 49 study markers, MiniJournalCluster hooks, node-startup brackets, the startup window, weak adapter registries, the NN heartbeat tick, the IPC door naming its verb) + `gc/hdfs-study-startup` (the NN's `registerDatanode` write lock as the startup step). Maven repo `/bigtemp/vnr3ne/m2/hdfs-study-next`. Clean. Its surefire reports were written by a study-next run; `experiments/hadoop/classpath.py` takes their entries from r3. |
| `/bigtemp/vnr3ne/wt/hadoop-hdfs-study-r4` | `gc/hdfs-study-r4` `42f029cc568` (WIP) | r3 + the IPC handler opens a call's exchange before `doAs` (`Server.Handler#work`, `Call#causynthEnter/Exit`, `RpcCall#run` back to upstream) + DataXceiver's redundant hand `endInbound()` removed. **Not built**; Maven repo `/bigtemp/vnr3ne/m2/hdfs-study-r4` (copied; may hold partly installed artifacts). Becomes the HDFS tree once validated (TODO HDFS §2). |
| `/bigtemp/vnr3ne/wt/hadoop-hdfs-11741-verb` | `gc/hdfs-11741-verb` `0d24b5f626b` | hdfs-11741. Maven repo `/bigtemp/vnr3ne/m2/hdfs-11741-verb`. Clean. |
| `/bigtemp/vnr3ne/wt/hadoop-hdfs-11741-r4` | `gc/hdfs-11741-r4` `a703b618d34` (WIP) | 11741-verb + the same handler change. **Not built**; Maven repo `/bigtemp/vnr3ne/m2/hdfs-11741-r4`. |
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

Per check: [../checks/README.md](../checks/README.md). Summary (46 HDFS cases):
- known bugs: 9 PASS; hdfs-11741's witness confirmed but its key-id binding unstable (TODO);
- study: 7 verdicts on the merged body (10 12 SAT; 11 15 16 19 20 UNSAT) + 10 UNSAT on the previous body to rerun
  (27 28 29 30 31 39 40 48 49 52); 8 open with a fix landed or a rerun owed (07 08 09 24 26 33 37 50); 2 open with the
  defect named (14: the r4 handler fix; 32: an unversioned map read); 9 in the time-model class (01 17 21 22 23 25 34
  35 43);
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
