# START HERE: GraphChecker's ZooKeeper ad hoc checks (finished 2026-10-22)

You take over a finished system. This file is self-contained: what was done, where every piece is, how to run a case
and the whole series, what is left, and the rules.
- **Repo:** `/u/vnr3ne/GraphChecker`, GitHub `git@github.com:JHSUYU/GraphChecker.git`.
- **Branch:** `system/zookeeper`, worktree `/bigtemp/vnr3ne/wt/gc-zookeeper`. It is local; pushing GraphChecker needs the
  owner's OK.
- **Engine:** HBase's final engine (`system/hbase` 5b4b6bae9) plus this session's ZooKeeper work (STATE §Z).
- **Tree:** the fork https://github.com/JHSUYU/zookeeper, branch `graphchecker/zookeeper-checks` (local repo
  `/u/vnr3ne/zookeeper`, branch `gc/zk-checks`).
- **Finished systems:** HDFS, Solr, HBase and ZooKeeper. STATE §0, §S, §H and §Z describe them, each on its own branch.
  HBase's takeover file is [hbase-START-HERE.md](hbase-START-HERE.md).

## 1. The goal and the result

The owner (2026-10-21): "接下来的下一步，我要做zookeeper上的adhoc check。类似hbase。然后zookeeper上呢，我们本来已经有了些adhoc check的
target，需要囊括这几个bug。这几个bug也要选adhoc check，看合适的workload。用一样的hbase规则". So ZooKeeper's ad hoc checks ran the
way HBase's did, under the same rules, with the same kind of adaptation: an automatic cluster, a message door per wire,
and typed FAULT doors.

The session (a lead and five coding agents) did the following:
- **A:** the tree and the client-level cases.
- **B:** the two quorum-bug workloads.
- **C:** the automatic quorum cluster.
- **D:** the learner-stream door and zxid carriage.
- **E:** the engine and VM defects.

Every piece was merged into `system/zookeeper` and `gc/zk-checks` in integrations 6-13, then the final series ran
(`results/zookeeper/`).

**The 16 cases.** `docs/checks/ZOOKEEPER.md` §E has each one's marker, workload, counterfactual and fit. Each is one
STATUS row ("ZooKeeper checks") and one `results/zookeeper/` file (`results/zookeeper/README.md` has the time/region table).
A run tag marked PENDING is a case of the alone round F2, rerun because its concurrent run took over 30 min.

| case | what | final verdict (run) |
| --- | --- | --- |
| zk-bugs-quota-init | **the partial quota**: createQuota's limit node without its stat node | **PASS**: SAT MARKER_FLIPPED (valuation 1, the ZOOKEEPER WRITE fault), native 10/10 (F1C-quota, 270 s) |
| zk-bugs-election-offer | **the orphaned election offer** | **PASS**: SAT STATE_PAIRING_FLIPPED (valuation 0), native 10/10 (F1C-offer 2326 s; F2B-offer PENDING) |
| zk-bugs-container-reuse | **the container cleanup** deletes a replacement at the same path (A's widened-window workload) | **PASS**: SAT STATE_PAIRING_FLIPPED (valuation 0), native 10/10 (F1B-cont, 572 s) |
| zk-bugs-retry-seq-quota | bug_study #32: ZooInspector's retry re-creates a sequential node | **PASS**: SAT MARKER_FLIPPED (valuation 1), native 10/10 (F1C-rseq, 350 s) |
| zk-bugs-trunc-sync | **ZOOKEEPER-5094 (PR 2459)** | **not detected** (owner): UNSAT_CLOSED at depth 1 (F1B-trunc 1916 s; F2B-trunc PENDING). ZB15 reached life 2's FAULT world, but that world also fails life 3's log open (TODO ZooKeeper 1) |
| zk-bugs-observer-master | **ZOOKEEPER-5088 (PR 2454)** | **PASS**: SAT STATE_PAIRING_FLIPPED (valuation 0), native 4/10 (F1F-om on int-13, 494 s, concurrent) |
| zk-adhoc-01 | study §D: the leader's checkSession (session expiry) | SAT_UNCONFIRMED: every claim refused in its confirmation replay, the normal FP filter (F1S-01 2536 s; F2S-01 PENDING) |
| zk-adhoc-02 | study: SessionMovedException (session.owner re-pairing) | PENDING (F2S-02; ZE8-02: SAT_UNCONFIRMED, every claim refuted by CONFIRM, the FP filter) |
| zk-adhoc-03 | study: the expirer's SessionExpired at setOwner | SAT CLOCK_SKEW (the expirer turn's clock), confirmed, native 4/10 (F1C-03, 423 s) |
| zk-adhoc-04 | study: ReadOnlyModeTest#testSeekForRwServer | PENDING (B: F1E-04 on trees-12, the RO client's constant host seed) |
| zk-adhoc-06 | study: Leader#waitForEpochAck | UNSAT_CLOSED, substantive (F1S-06, 964 s) |
| zk-adhoc-07 | study: Learner#registerWithLeader's epoch check | UNSAT_CLOSED, substantive (F1S-07, 829 s) |
| zk-adhoc-10 | study: ObserverMaster#proposalCommitted's head check | UNSAT_CLOSED, vacuous by construction, class C (F1S-10, 1016 s) |
| zk-adhoc-11 | study: QuorumPeer#loadDataBase's epoch files | UNSAT_CLOSED, vacuous by construction, class C, IO rule (F1C-11 2968 s; F2S-11 PENDING) |
| zk-adhoc-12 | study: QuorumPeer#loadDataBase's acceptedEpoch < currentEpoch | UNSAT_CLOSED, substantive (F1C-12, 996 s) |
| zk-adhoc-13 | study: ReadOnlyModeTest#testConnectionEvents | UNSAT_CLOSED, substantive (F1E-13 on trees-12, 229 s) |
| (05, 08, 09) | selected, not run: a dead throw, no path (`docs/checks/SELECTION.md`) | - |

The owner named five bugs: quota-init, election-offer, container-reuse, trunc-sync (5094) and observer-master (5088); retry-seq-quota (bug_study #32) is the sixth bug check. A bug check is done when it is SAT, confirmed in the VM and reproduced natively, with
the bug's causal chain. A study check is done at SAT, UNSAT (read with `vacuity.py`) or a named bound.

## 2. Read, in this order

1. This file, then [STATE.md](STATE.md) §Z: branches, tree, snapshots, images, tree sets, run dirs, evidence.
2. `results/zookeeper/README.md`: the final table and one reading per case.
3. [TODO.md](TODO.md) "ZooKeeper": what is left, each item parked with its evidence.
4. [LESSONS.md](LESSONS.md) §10 (ZooKeeper's traps), §9 (HBase's, which still apply), and the rest.
5. `docs/checks/ZOOKEEPER.md` §E (the cases) and STATUS "ZooKeeper checks" and "Per-system surface" (every tree
   workaround, ZooKeeper column).
6. [RULES.md](RULES.md), [CHECKING.md](CHECKING.md), [OPERATIONS.md](OPERATIONS.md) §10, [AGENTS.md](AGENTS.md),
   [PARALLEL.md](PARALLEL.md).
7. `docs/design/PIPELINE.md` for the stage you touch; `docs/design/IDENTITY.md` for nodes, contexts, hand-offs and queue
   items.

## 3. What is left

TODO "ZooKeeper" lists each item with its evidence; none blocks a verdict:
- 5094's seed re-run for seed-only exposures (designed, not built);
- EXPLORE re-pairing a container read;
- static candidates over NOT_ADMITTED replays;
- the consumer-side moved-roots filter;
- the learner envelope's own fields;
- the reply -> synchronous-caller edge (TODO HBase 15);
- CONFIRM over an unproducible planted answer (STATUS open defect 72);
- the learner stream's racing ACK hand-overs.

Open from the final series:
- 02 and 04 are pending (F2S-02 alone; B's F1E-04).
- om reproduces 4/10 natively, and 03 does too.
- The fork's `graphchecker/zookeeper-checks` is still at integration 10 (442c88199). Push the final tree `gc/zk-checks`
  2b6e17bf8 and `gc/zk-hostseed` 51b213562; the fork may be pushed, apache never.

## 4. Running a case and the series

Mechanics as HBase's (OPERATIONS.md §10).
1. **Snapshot** `system/zookeeper`:
   ```
   flock /localtmp/vnr3ne/worktree-add.lock bash tools/lib/worktree-add.sh /u/vnr3ne/gc-run/<name> <commit> --detach
   ```
   Always give an explicit commit: `HEAD` resolves in the main repo. Then run `mvn -q -o package -DskipTests` on a lift.
   Never rebuild a snapshot a run reads.
2. **Tree set:** `git -C /u/vnr3ne/zookeeper worktree add --detach <dir>/zookeeper-checks <tree commit>`, then
   ```
   env -u BASH_ENV tools/onlift.sh -h <host> -g 8 env GC_TREES=<dir> ZOOKEEPER_MAVEN_REPO=<repo> bash experiments/zookeeper/prepare-trees.sh
   ```
   It installs each workload module and runs each workload natively (PASSED/FAILED per case). `onlift.sh` forwards no
   environment: put the variables inside the command. Never rebuild a tree set a run reads, and never run natives on it.
3. **One case**, from a head that reaches every worker (never lift02/03 or the lead's gate host):
   ```
   CAUSYNTH_CUSTOM_JDK_HOME=/bigtemp/vnr3ne/vm-force13/j2sdk-image GC_TREES=<dir> GC_OUT=<out> tools/rounds/launch-run.sh <snapshot> <case> <tag>
   ```
   The detached form is `/bigtemp/vnr3ne/analysis/zookeeper-2026-10-21/lead/launch.sh <topic> <snapshot> <case> <TAG>
   <budget>`, with `wait-run.sh` to wait. `STOP_AFTER=SEED` lists the observed occurrences when a target selector is
   unobserved: read a selector that way, then write it into `case.sh` / `checks.tsv`.
4. **The series:** `/bigtemp/vnr3ne/analysis/zookeeper-2026-10-21/lead/final/` (PLAN.md):
   - `SNAP=... TREES=... series.sh <round> <concurrency> <case>...`: F1* concurrent (runs under 30 min), F2*/F3* alone on
     all 14 hosts.
   - `final-stats.py --order ... --cases <SNAP>/experiments/zookeeper/zookeeper-cases.tsv` prints the table.
   - `SNAP=... ORDER=... collect-results.sh <repo>` fills `results/zookeeper/`.
   - Or the generic `tools/rounds/run-series.sh <round> experiments/zookeeper/zookeeper-cases.tsv
     system/zookeeper=<snapshot>`.
5. **After a case:**
   - run `tools/analysis/vacuity.py --latest --detail <run>` on every UNSAT;
   - read the `.smt` with `tools/analysis/smt-legend.py`;
   - update the §E row and the STATUS row.

Per-case settings live in `experiments/zookeeper/zk-bugs/case.sh`, `zk-adhoc/checks.tsv` and `case.sh`, and
`workflow.properties`: target selectors, world depth, claim cap, CONFIRM order timeout, client-fault cut and scope.
PLAN.md §2 tabulates them.

## 5. Rules you must keep (RULES.md and LESSONS.md have each)

- General fixes only. A per-system adapter piece or workaround is small and named in STATUS "Per-system surface". A
  workaround may make an order controllable or a value trackable; it never switches the fatal outcome.
- Reuse the existing adapter shapes: HBase's CausynthHBaseCluster/CausynthRpc, HDFS's IPC door, Solr's ZooKeeper store hooks.
  Name the closest one for each new piece.
- Read the existing mechanism before building one. Time-box an engine challenge to about 45 min, then work around it
  (owner). The time model is handled by workarounds only. The owner's ruling on 5094 (2026-10-21): "我觉得你搞简单点吧，
  没必要为5094花这么多时间" -- an engine change for one case stops when it grows.
- Measure first, prove the mechanism, then fix. Completeness > precision: over-approximate in COMPOSE, confirm strictly.
  The false-positive filter (CONFIRM/REPRODUCE) is kept ("02这种如果是正常的false positive过滤你要保留").
- A roughly right `.smt` per case is the bar (owner 2026-10-20).
- ZooKeeper changes are judged by ZooKeeper's cases only.
- Java 8 for every workload. Workloads are existing unit tests where one exercises the bug; a self-written
  `Causynth*Test` only where none does, and it must pass natively on the buggy tree.
- Per-case run settings live in `case.sh` / `workflow.properties`.
- The final series: runs under 30 min may run concurrently; every longer case runs alone on all 14 hosts; scope a
  too-slow case.
- Heaps: replays and solvers use at most 70 % of a host; a head is charged its heap for life.
- Shell and git:
  - Always `env -u BASH_ENV`. Kill only by explicit pid. Never `git add -A`. Never `rm -rf $VAR/...` unquoted.
  - Never `git branch -f` a checked-out branch. After a merge, check `git status` for unmerged paths.
  - Commit trailer: `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`.
  - Push GraphChecker only with the owner's OK. The ZooKeeper fork may be pushed; apache never.
- Decide engineering yourself and report. At most 5 coding agents.

## 6. Where things are

STATE §Z has the full list. In short:
- **GraphChecker:** `system/zookeeper` at `/bigtemp/vnr3ne/wt/gc-zookeeper`.
- **Final snapshot:** `/u/vnr3ne/gc-run/zk-int-13` (system/zookeeper d73c28302). The int-12 runs (d4fbcd97c) stand: int-13
  adds only D's COMPOSE fix, and an offline A/B is identical except om.
- **Tree:** `/u/vnr3ne/zookeeper`, `gc/zk-checks` = the fork's `graphchecker/zookeeper-checks`. Final tree set:
  `/bigtemp/vnr3ne/wt/zk-int-trees-11` (2b6e17bf8) for every single-host case, and `zk-int-trees-12` (`gc/zk-hostseed`
  51b213562, the RO client's constant host seed) for 04 and 13.
- **VM image:** `/bigtemp/vnr3ne/vm-force13/j2sdk-image` (vm-force12 plus the failed-CAS answer).
- **Runs:** `/bigtemp/vnr3ne/gc-out/zookeeper-final` (the series) and `zookeeper-{tree,qwork,quorum,learner,engine}` (the
  agents' runs).
- **Evidence:** `/bigtemp/vnr3ne/analysis/zookeeper-2026-10-21/` (lead/RUNS.txt: every run and decision;
  lead/readings.md; lead/final/).
- **Hosts:** lift02-15, 48 cores and 30 GB each.
