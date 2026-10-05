# State at the handover of 2026-10-04 night

The owner stopped the lead and every agent ("请你停止所有的agent。停下当前的活…我的目标是别的coding agent读了你这个文档可以快速接手").
Nothing runs on any lift: HG5 was stopped about 25 minutes after its launch, and both coding agents
committed their WIP and stopped. Read this file, then [TODO.md](TODO.md), [RULES.md](RULES.md),
[AGENTS.md](AGENTS.md) and [OPERATIONS.md](OPERATIONS.md). The design is in [../design/](../design/README.md),
and what is done / partial / missing per requirement is in [../STATUS.md](../STATUS.md).

## 1. The goal (verbatim, owner, 2026-10-04) and what it means

> 请你阅读graphchecker的source code和vm代码。先了解这个Tool在处理的adhoc coordinaiton。以及我们的处理方式。然后阅读graphchecker远端study分支上的study.txt。里面记录了4个system的adhoc coordianotin位置，以及他们对应的cluster based unit test。同时，~/bug_study下是一些可能是adhoc coordianot有关的bug。请你仔细阅读graphchecker的readme。给每一个系统上，adhoc coordiaont check都加上我们的annotation。并编号，然后去check他们。~/graphchecker里的readme描述了我们已经在check的10几个adhoc coordiaotn bug。有些跑通了有些可能还没有。他们都要跑通然后你完成todo。最终我们的目的是，四个system。我们的graphchecker创建四个对应分支。这四个分支代码主体都是一样的。只是每个system可能有一些小适配，workaround。你去检查所有study分支下.txt的内容，以及我们的新bug，你去check一下如果发现那个点确实是adhoc coordianot，并且有unit test。或者，新bug是adhoc coordiaont。（而且这个bug确实能被我们当前graphchecker的方式check到。如果这个bug的某些操作。比如io让symbooic 断了那肯定不行。最好这个bug能跟我们ahdoc cordianot study.txt里。或者这个新bug真的很高质量，确实是adhoc coordiaont。只是我们study.txt每包含。 重复在一个已有/或者这个bug很高质量，你自己写一个unit test)。这个bug的整个路径，符号传播都能确实被我们的模型include到.smt里，这个新bug才能在我们的adhoc ehck里。总之每个系统上我们就要检查若干adhoc coordination。跑出他们的.smt。如果这个点包含我们已有的bug。那应该是.smt跑通。然后你最终跑完这4个system上所有adhoc check。

In short:
- Four systems: HDFS, Solr, HBase, ZooKeeper.
- One GraphChecker branch per system (`system/<sys>`): the same engine body, plus small per-system
  adapters and workarounds.
- Every selected ad hoc coordination point is marked in the system's tree with
  `@CausynthExceptionTarget("<sys>-adhoc-NN")` and checked with its cluster test. The selection is
  the owner's narrowed subset of the study's points (§3).
- Real bug_study bugs that GraphChecker can check are added. Each was verified in the code
  (`/bigtemp/vnr3ne/analysis/study-2026-10-04/VERIFIED.md`).
- Every check ends with an exported `.smt` whose verdict is SAT (confirmed) or UNSAT, and the
  `.smt` is right: causal chain, symbols and propagation, read against the code.
- Every known bug must pass.
- The systems go one at a time, in the order HDFS, Solr, HBase, ZooKeeper. **This round is HDFS
  only** (owner: "你本轮只要跑通hdfs的即可。别的系统先不管").

## 2. Branches (GraphChecker repo `~/GraphChecker`, remote `origin` = github)

| branch | head | worktree | what | remote |
| --- | --- | --- | --- | --- |
| `system/hdfs` | this handover's docs commit, on the `hg5` integration | `/bigtemp/vnr3ne/wt/gc-hdfs` | **The HDFS GraphChecker branch, and the newest engine body.** It is built, unit-tested (342) and shell-tested. Its last complete live round was HG4, on `hg4` = `2680e7f63`. HG5 (this body) was stopped before any verdict. It contains `hg4` (seed-stalls, campaign-schedule, observed-arm, explore-planning, decisive-verdicts at `25e548b54`), scope batch 1 (`hdfs-scope-slice`, `-container`, `-rows`, `-iofault`), the VM sources of image `vm-hg5` (`hdfs-vm-hg5`), the remote-CONFIRM wait and reserve fixes (`71df98a00`), and the case declarations on the r3 tree. | pushed with this handover |
| `hg5` | = `system/hdfs` | `/bigtemp/vnr3ne/wt/gc-hg4b` | the integration branch the HDFS work was built on (worktree name from HG4); `system/hdfs` was fast-forwarded to it at this handover. Use one of the two for the next integration and delete the other | local |
| `hdfs-decisive-verdicts` | `66c22f440` (WIP, **not built**); `c76be91a7` is the last built and tested commit | `/bigtemp/vnr3ne/wt/gc-hdfs-decisive-verdicts` | The second review's FIX FIRST list for "only SAT/UNSAT" (brief `/bigtemp/vnr3ne/analysis/study-2026-10-04/brief-decisive-fix2.md`). Done: item 1 first half (cone.py exemption reverted, `0219d06b8`) and item 6 (`AMBIGUOUS_FATAL_ARM` is a BLOCKING gap, `c76be91a7`). Partly done in the WIP: items 3 and 4. Not done: 2, 5, 7. | local |
| `hdfs-draw-sites` | `3a27177b3` | `/bigtemp/vnr3ne/wt/gc-hdfs-draw-sites` | **HG6**: site-keyed random draws and "pre" startup marks (`fd3d97403`), the T1 hold (`7de198e7d`), a node startup ends the exchange its thread served (`3950fe768`, engine side of the R3 fix), C1 removed (`3a27177b3`). 333 tests and the shell test pass. Based on `d916851fa` (seed-stalls before campaign-schedule): it runs CONFIRM inline, so merging it into `system/hdfs` needs care in `run_engine.sh`. Not merge-ready: canaries, V25 gate and review pending. | local |
| `hdfs-clock-replay` | `22520bf02` | none | C1 (keyed clock replay), parked. Its commit message has the findings of rounds DS2–DS7 and the start-up time model a correct version needs. | local |
| `main` | `fe3a5f1a0` | `~/GraphChecker` | the 2026-10-03 handover body (V25 14/14) | pushed |
| `system/solr`, `system/hbase`, `system/zookeeper` | `fe3a5f1a0` (= main) | `/bigtemp/vnr3ne/wt/gc-{solr,hbase,zookeeper}` | created for the 2026-10-04 goal; nothing on them yet (their systems' turn comes after HDFS) | local |
| `study` | `8d9621e7a` | `/bigtemp/vnr3ne/wt/gc-study` | `study.txt` (the static study: 144 YES points with cluster tests) and `selection.txt` (the owner's narrowed selection per system) | pushed |
| `solr-bug-reindex` | `12283e3f1` | `.claude/worktrees/agent-a6cdfa854234df67e` | Solr #04 + Solr replay fidelity (store-write turn, stall rules, recorded draws, `AT_QUESTION_CLOSED`, explore queue rules, `RECORDING_STALLED`). Round SBR26: 13/14, **solr-18413 regressed** (seed replay hit 2400 s in 103,812 stalls: a WRITE `SOLR_ZK:/overseer/queue/qn-` held at its slot while the Overseer's poll ran past its recorded WAKE count). SBR26b was stopped in SEED (2.1 GB trace at 2 GB heap). Parked by the HDFS refocus. | local |
| `hb-schedule` + `hb-sync` | `1fb4a475a`, `53f16e8b6` | `.claude/worktrees/agent-aea16c87adafb5d81` | One per-session happens-before relation, replacing anchor ancestry, plus signal and store-notification edges and CONFIRM's single question rule. Every review item is fixed. Next: the offline gate on V25, then live ZooKeeper cases and 11741. | local |
| `hbase-startup` | `3afb27f13` | `/bigtemp/vnr3ne/wt/gc-hbase-startup` | HBase #14 (opt-in startup window, interface-delegate clock rule, per-waiter WAKE count). HBA3 showed two blockers: (1) threads started by libraries (ZooKeeper EventThread, Netty event loops) inherit their racing creator's frames, 34 stalls; (2) the RS's report value is exported on one thread and sent by another after a queue, so the attach at the new master stays constant. Both need a lead design decision. | local |
| `wire-codec-p1` | `3e9cb3182` | `.claude/worktrees/wire-codec-p1` | WIRE-CODEC (codec ports by rule, W6 HDFS envelopes, LEAF round-trip contract). Canary 17897 PASS; 11741 had no verdict. Spec: `/bigtemp/vnr3ne/specs/WIRE-CODEC-proposal.md`. | local |
| merged feature branches | | many `/bigtemp/vnr3ne/wt/gc-hdfs-*` worktrees | All contained in `system/hdfs`: `hdfs-campaign-schedule`, `-carried-turns`, `-compose-refusals`, `-explore-planning`, `-loop-body-entry`, `-node-names`, `-start-carries-node`, `-observed-arm`, `-replay-stalls`, `-review-fixes`, `-runtime-config`, `-scope-*`, `-seed-scale`, `-seed-stalls`, `-start-verb`, `-vm-hg5`, `-replay-windows`, `-runtime-fixes`, `-node-startup`, `-startup-own-work`, `-construction-only-stores`. `hdfs-construction-only-values` (`ca50b8319`) is parked: it needs an 11741 chain check. | delete at cleanup |

The older branches of the 2026-10-03 handover that are merged into `main` (`system-zookeeper`,
`vm-streams`, …, `main-v25`) and the superseded ones (`recording-stall-guard`, `fix-no-root`,
`system-hbase`, `replay-heap-bound-store`, `state-pairing`, `fix-hdfs-seed-stalls`,
`worktree-agent-a49c8bf5715a00c40`) are deletable. Bundles of earlier deleted branches and old WIP
patches are in `/bigtemp/vnr3ne/handover/`.

**How the four system branches relate.** The engine body has moved forward on `system/hdfs` all
through 2026-10-04: about 25 merges since `main`. When HDFS is done, `system/hdfs`'s body goes to
`main`, and `main` is merged into `system/solr`, `system/hbase` and `system/zookeeper`. Each of those
then adds only its system's adapter, declarations and cases. Do not develop the engine separately
on two system branches.

## 3. The checks (owner's narrowed selection, 2026-10-04)

| system | points | checked | study checks | bug checks | cases | where the list is |
| --- | --- | --- | --- | --- | --- | --- |
| HDFS | 38 | 36 | 36 | 10 | **46** | `experiments/hadoop/hdfs-adhoc/checks.tsv` (each row: id, test class, method, window, target selector) + the named cases |
| Solr | 21 | 13 | 13 | 7 (+ solr-adhoc-22 = solr-18406) | 20 | `selection.txt` (branch `study`), `/bigtemp/vnr3ne/analysis/study-2026-10-04/{SELECTION.md,solr.md}` |
| HBase | 30 | 17 | 17 | 3 | 20 | same, `hbase.md` |
| ZooKeeper | 13 | 10 | 10 | 3 | 13 | same, `zookeeper.md` |

The study's ids never move (`hdfs-adhoc-NN`, `solr-adhoc-NN`, `hbase-adhoc-NN`, `zk-adhoc-NN`).
HDFS checked points:

```
01 07 08 09 10 11 12 14 15 16 17 19 20 21 22 23 24 25 26 27 28 29 30 31 32 33 34 35 37 39 40 43 48 49 50 52
```

HDFS 13 and 18 are selected points with no check.

The trees: the HDFS trees mark all 49 study points plus the bug targets. The Solr, HBase and
ZooKeeper trees mark only their bug targets so far. Their study markers are a TODO of their turn.

**The known bugs** (19 bugs, 23 cases, plus hdfs-11741):

| system | case | bug | mechanism | status |
| --- | --- | --- | --- | --- |
| HDFS | hdfs-11741 | stale block key after expiry (its own tree `gc/hdfs-11741-verb`) | CLOCK_SKEW | HG4: confirmed CLOCK_SKEW witness lost to the remote-CONFIRM wait bug, then EMIT killed at the case timeout. Both fixed in `71df98a00`. |
| HDFS | hdfs-17897 | striped checksum treats `InvalidEncryptionKeyException` as an I/O failure (PR #8364) | IPC door fault | PASS (HG4) |
| HDFS | hdfs-17899-bug1/2/3 | a failed key-refresh RPC leaves a stale data-encryption key (Balancer / SPS / source DN) | IPC door fault | bug1, bug3 PASS. **bug2 FAIL**: lost key-id binding, cause found (see TODO) |
| HDFS | hdfs-17967-pathA/B/C | three DN relay paths abandon on `ERROR_UNKNOWN_KEY` instead of refreshing | IPC door fault | PASS (HG4) |
| HDFS | hdfs-17960 | ordered=false lets a duplicate delete record decrement `numSnapshots` (PR #8672) | CONFIG | PASS (HG4) |
| HDFS | hdfs-bugs-slowdisk-zero | bug_study HDFS #15: max slow disks 0 leaves a stale exclusion list | STATE re-pairing | PASS (HG4) |
| Solr | solr-18406 (= solr-adhoc-22) | the leader deletes a generation after the reservation expires | CLOCK_SKEW | PASS on main (V25) |
| Solr | solr-18413 | a MIGRATE route rule expires; the update looks up a deleted collection | CLOCK_SKEW | PASS on main (V25); regressed on `solr-bug-reindex` |
| Solr | solr-bugs-reindex-cleanup | #04: a failed same-target reindex leaves the alias; cleanup throws | ZK/HTTP door fault | no witness yet (`solr-bug-reindex`) |
| Solr | solr-bugs-migrate-buffer-leak | #17: a failure after REQUESTBUFFERUPDATES leaves the target core BUFFERING | door fault | admitted, no case yet |
| Solr | solr-bugs-overseer-lock-leak | #50: OperationTimeout in markTaskAsRunning leaks the lock; the task never runs | ZK door fault (OperationTimeout) | admitted, no case yet |
| Solr | solr-bugs-snapshot-no-active | #16: CREATESNAPSHOT skips non-ACTIVE replicas and reports success | stale Overseer view (CLOCK or STATE) | admitted, no case yet |
| Solr | solr-bugs-restore-construction | #26: a failed RESTORE leaves slices in CONSTRUCTION; the retry never fixes them | HTTP door fault | admitted, no case yet |
| Solr | solr-bugs-tra-start-overwrite | #20: TimeRoutedAlias writes a stale aliases snapshot over a newer alias | STATE re-pairing | admitted, no case yet |
| HBase | hbase-bugs-master-active-time | #14: a non-monotonic wall-clock activeTime makes the new master reject an old OPENED report | CLOCK | `hbase-startup`, blocked (two design questions) |
| HBase | hbase-bugs-backup-lock-reply-lost | HBase-2 #16: a lost CAS reply makes the retry fail on the client's own lock | HBase RPC RESPONSE door | admitted, no case yet (needs an HBase RPC door) |
| HBase | hbase-bugs-ns-rsgroup-removal | HBase-2 #01: rsgroup removal cannot see an in-flight namespace creation | STATE re-pairing | admitted, no case yet |
| ZooKeeper | zk-bugs-quota-init | #01: the quota limit is committed before the stat node; the retry gets NoNode and the hard quota is bypassed | ZK write door fault | PASS on main (V12+) |
| ZooKeeper | zk-bugs-election-offer | #05: a competitor's offer vanishes before `getData` | STATE re-pairing | PASS on main (V18+) |
| ZooKeeper | zk-bugs-container-reuse | #33: ContainerManager deletes a node recreated at the same path | STATE re-pairing | admitted, no case yet (self-written ClientBase test) |

Real but not admitted:
- HDFS-2 #09 reencrypt-negative-sleep: the chain ends in a JDK-internal negative-sleep exception; dropped after HG1.
- ZooKeeper #32: a contrib GUI tool, too low in quality.

## 4. HDFS rounds of 2026-10-04 and the state of each check

Rounds (sweeps of the HDFS group). Outputs are `/bigtemp/vnr3ne/gc-out/hdfs-study/accept-<round>-<n>/`; the
case lists and reviews are in `rounds/`.

| round | snapshot (body) | result |
| --- | --- | --- |
| HG2 | a179dd815 | named 4/4 that ran PASS; 6 SEED loop-id stops (fixed) |
| HG3 | `~/gc-run/hg3` | first full run of the 46; review `rounds/HG3-review.md` |
| HG4 | `~/gc-run/hg4` = `2680e7f63`, tree r3, image `vm-size-source` | named: 8 PASS (17897, bug1, bug3, 17960, pathA/B/C, slowdisk), bug2 FAIL, 11741 timeout. Study: 23 UNSAT, 3 SAT (10 and 12 confirmed witnesses, neither a new bug; 32 fatal in the recording), 10 without a verdict. Review `rounds/HG4-review.md` |
| HG5 | `~/gc-run/hg5` = `e76f6b4a8`, tree r3, image `vm-hg5` | launched 22:30, **stopped by the owner** after ~25 min: no verdicts |

Per check (HG4 unless noted):

| state | checks |
| --- | --- |
| UNSAT with exported `.smt` (provisional: the decisive-verdicts fix list still touches the formula's FREE/pinned values) | 07 08 09 11 14 15 16 19 20 26 27 28 29 30 31 33 37 39 40 48 49 50 52 |
| SAT, confirmed | 10 (QJM, the designed tolerance), 12 (the 17899/17967 root cause at study point 12) |
| SAT with no root moved: the target threw in the recording | 32 (HG6 removes that throw: its deleteBlockPool #3 no longer throws) |
| no verdict, start-up family | 21 22 23 24 25 34 35. Cause: the T1 hold placement plus R3's single anchor, made worse by the keyed clock replay C1 (the DN heartbeat schedule is set from the live clock during start-up). On HG6 without C1, 22 and 34 reach their targets. |
| no verdict, clock/draw class | 01 17 43 (HG6 probes: 17 still 52 give-ups, 43 1, 01 not rerun) |
| no verdict, other | 11741 (fixed, see above) |
| efficiency items | QJM 07/08/09 ~82 min and 15 ~61 min. EXPLORE is dominated by obligations refused at planning (ADMISSION_GAP). 16: after the refutation, the re-compose hit a z3 timeout. 07: self-contradictory paths. |

New HDFS bugs found: none so far. Per the owner, a right `.smt` with no new bug is an acceptable outcome.

## 5. Trees, VM images, snapshots

| tree | branch, head | used by |
| --- | --- | --- |
| `/bigtemp/vnr3ne/wt/hadoop-hdfs-study-r3` | `gc/hdfs-study-r3` `d03c1f9134a` | **every HDFS case but 11741** on `system/hdfs`. It is `gc/hdfs-study-next` plus `gc/hdfs-study-startup`: the NameNode's `registerDatanode` write lock is the startup step that fixes the DataNodes' order. Maven repo `/bigtemp/vnr3ne/m2/hdfs-study-next`. |
| `/bigtemp/vnr3ne/wt/hadoop-hdfs-study-next` | `gc/hdfs-study-next` `614a077ed30` | base of r3: the 49 study markers, MiniJournalCluster hooks, node-startup brackets, the startup window, weak adapter registries, the NN heartbeat tick, the IPC door naming its verb |
| `/bigtemp/vnr3ne/wt/hadoop-hdfs-11741-verb` | `gc/hdfs-11741-verb` | hdfs-11741 |
| `/bigtemp/vnr3ne/wt/hadoop-hdfs-study-startup` | `gc/hdfs-study-startup` | merged into r3; delete at cleanup |
| Solr / ZooKeeper / HBase trees | `gc/solr-bugs` `f65aaf7`, `gc/solr-unified-storing` `04f8489`, `gc/solr-unified-storing2` `40b7659`, `gc/zk-unified` `8f18cf3a4`, `gc/zk-unified-hb` `47ddc8b36`, `gc/hbase-unified` `1051825287` | the main/branch cases (see [OPERATIONS.md](OPERATIONS.md) §2) |

VM images:
- `/bigtemp/vnr3ne/vm-hg5/j2sdk-image` belongs to `system/hdfs`: container iterators, read records
  stating their version, outside-mutation marks. `SOURCE.txt` in that directory says which sources
  built it.
- `vm-size-source` served HG4.
- `vm-model-guards2` serves `main`.
- `vm-hdfs-scope-container` and `vm-hdfs-scope-rows` were the agents' builds and are superseded by
  `vm-hg5`.

Snapshots in `~/gc-run/`:
- `hg4` and `hg5` are the latest rounds' bodies.
- `hds8` is HG6's probe body: `3a27177b3`, with case repos edited to r3 in the snapshot only.
- Every other snapshot (`hcs-*`, `hdv*`, `hg3`, `hg5b`, `hg5m`, `hoa*`, `hsc*`, `hscope1`, `hsr1`,
  `hssp1`, `iof*`) is stale. Remove them with `tools/rounds/snapshot-gc.sh`.

## 6. Where the analyses live

- `/bigtemp/vnr3ne/analysis/study-2026-10-04/`:
  - `SELECTION.md`: the narrowed selection with reasons.
  - Per-system study tables `hdfs.md`, `solr.md`, `hbase.md`, `zookeeper.md`: per point the site,
    guard, coordination, test and fit. The Solr, HBase and ZooKeeper turns start from these.
  - `VERIFIED.md`: the lead's code reads of each admitted bug.
  - `AGENT-RULES.md`: the rules every coding agent follows.
  - `brief-decisive-fix2.md`: the in-flight fix list.
- `/bigtemp/vnr3ne/analysis/unify/{hdfs,solr}-inventory.md`: commit-by-commit inventories of the
  unified HDFS and Solr trees.
- `/bigtemp/vnr3ne/specs/`:
  - `WIRE-CODEC-proposal.md`: the WIRE-CODEC spec. Its decisions bind.
  - `R1-ROOTS-proposal.md` and `R3-REFCONT-proposal.md`: the root-demand and reference/container
    specs. Code comments and PIPELINE/SYMBOL-SCOPE cite their section numbers. Both were deleted
    with the other outdated specs on 2026-10-04 and restored the same night from their author's
    transcript (that agent's first full write plus its later edits), so a small in-place edit made
    after that by other means may be missing.
  - The other old specs (C2, F14, DOCS, R3-shapes), the 09-29 audit and the 10-02 code maps are
    deleted: outdated and cited nowhere.
- `/bigtemp/vnr3ne/handover/`: bundles of deleted branches and old WIP patches.
- `~/bug_study/*.txt`: the bug descriptions. `study.txt` and `selection.txt` are on branch `study`.
