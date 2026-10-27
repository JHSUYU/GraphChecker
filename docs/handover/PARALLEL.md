# Parallel development: keep ten lifts full (long-term)

Part of every agent's long-term memory ([RULES.md](RULES.md)). The owner, 2026-10-05: "一定要最大化利用10个server。这10个
server配有nfs,你只要做好代码隔离等。可以大大加速的。这是你的长期记忆", "我们一个case内oblication当然可以分配到多机。你也可以合理
利用nfs文件，只是做好隔离和共享", "我们不必强行要求独占", "我们的开发速度我觉得可以*10". The goal is the checks' right `.smt`;
the way there is that no work waits in series for anything but a real dependency.

## 1. Three levels of parallelism

| level | what runs at once | mechanism |
| --- | --- | --- |
| inside one case | its obligations (each a SOLVE, then a REPLAY when SAT), GROW's re-runs, CONFIRM, REPRODUCE's native runs | `run_engine.sh` streams them over every lift of `CAUSYNTH_CAMPAIGN_WORKER_HOSTS` (= `LIFTS`), each start charged on the host ledger; a head's engine JVMs go wherever there is room ([../design/PERFORMANCE.md](../design/PERFORMANCE.md) §2) |
| across cases | many campaigns, several rounds at once | `tools/adhoc/sweep.sh` (`heads-per-host`, a shared pool: each exploration takes its share of the slots and grows as others end); several sweeps side by side (one per purpose: a rerun group, the named-bug baseline, deep closures with a longer `CASE_TIMEOUT_SECONDS`); no case needs the cluster alone |
| across development | up to 5 coding agents (owner 2026-10-18; 4 before), read-only diagnosis and review agents, the lead's rounds | each agent on its own branch, worktree, snapshot and `GC_OUT`, up to four live runs at once; offline gates and builds via `onlift.sh` on the least loaded lift ([AGENTS.md](AGENTS.md)) |

The limits are memory and cores, both through the ledger: no lift above 70 % of its memory (the ledger refuses a start
past it, a running JVM past it is ended) and no lift with more cores charged than `CAUSYNTH_HOST_MAX_CORES_PCT` (100)
percent of its `nproc`, summed over every campaign on it. On liftlab (30 GB, 48 cores a lift) memory binds first; on
CloudLab (251 GB, 40 logical cores a node) cores do (round C1: nine campaigns, load 70-93, before cores were charged).

## 2. Isolation and sharing over NFS

Everything is on NFS (`~`, `/bigtemp/vnr3ne`), so every lift sees every file. That is what lets any start go to any
host, and it is why isolation must be strict.

- **Shared, read-only while in use:** the built system trees (`/bigtemp/vnr3ne/wt/hadoop-*` and their Maven repos
  `/bigtemp/vnr3ne/m2/<tree>`), the VM images (`/bigtemp/vnr3ne/vm-*`), the recorded corpora of rounds run with
  `PRUNE=0` (the offline gate's inputs), the host ledger (`$CAUSYNTH_HOST_LEDGER`, one for the cluster).
- **Worktrees without the VM's source:** 47,665 of the repository's 48,098 files are `third_party/` (the concolic
  VM), which no build or run reads. A full checkout writes them all to NFS (a worktree took 45+ minutes, a commit in
  it minutes); `tools/lib/worktree-add.sh <path> <commit> [-b <branch> | --detach]` leaves them out (10 s, `git
  status` 0.3 s, `mvn -q -o package` 27 s). Every snapshot and agent worktree is made with it; the VM's source is read
  or changed in a full checkout.
- **Isolated, one per run or agent:** a git worktree per branch (`/bigtemp/vnr3ne/wt/gc-<branch>`); a frozen snapshot
  per validated commit (`~/gc-run/<name>`, built once, never edited); a `GC_OUT` per agent and per round family
  (`/bigtemp/vnr3ne/gc-out/<branch>`, `hdfs-study` for the lead's HDFS rounds); a round name used once; replay scratch
  on the host's `/localtmp`.
- **Never:** rebuild a tree or snapshot someone's run reads (check `pgrep -f` on every lift first), write into another
  agent's `GC_OUT`, kill by pattern (kill by pid, `stop-run.sh` alone on its command line), install a tree into the
  shared `~/.m2` (`onlift.sh ... env MAVEN_REPO_LOCAL=... cmd`).
- **The control host stays light** (2026-10-12): the lead's and the agents' sessions all run on one lift (lift11), and
  every tool call starts a shell there. Their polling (one waiter per agent, from another lift, >= 60 s) and their
  heavy commands (`onlift.sh` off it) go elsewhere, and while they run there it is out of the campaigns' `LIFTS`; a
  jam on it stops every agent at once although the cluster and NFS are idle (OPERATIONS §8: `BASH_ENV` and a wedged
  `/sw`; the recipe: §6). Distribute through NFS as before: measured from the other lifts, NFS answered in milliseconds under ten
  campaigns; a git checkout per lift is not needed.
- **Host-dependent state is a hazard:** what differs between lifts or file systems (a directory's listing order, a
  temp path, a host name) makes a recording on one host and its replay on another disagree. The engine fixes such
  orders in both passes (random draws: `runtime/Randoms`; directory listings: `runtime/Listings`, merged), never by pinning work to
  one host.

## 3. The loop: nothing waits in series

1. **Run everything that does not wait on a pending fix, now.** At every lull, look at the lifts (memory and load on
   each) and fill them: the cases a fix does not touch, the named-bug baseline, deep closures with a longer budget,
   agents' probes.
2. **A landed fix is validated at once** on the cases it touches and a few canaries of other classes, in its own
   sweep, never by waiting for the next whole round. A whole round runs after a batch of fixes.
3. **Offline first:** a change to SEED's static pass, PLAN, EXPLORE's planning or COMPOSE is checked by
   `tools/regress/offline-ab.sh` on the `PRUNE=0` corpora in minutes; live runs only where the offline gate cannot
   see (VM, runtime, identity, schedule).
4. **Detection is automatic:** `round-watch.sh <round> <baseline>` names finished cases, seed replays past 30/80
   give-ups and STALLS-REGRESSION (twice the baseline's give-ups); `round-slow.sh` names cases past 2x/4x their
   baseline time; `round-verify.sh` checks every verdict (how EXPLORE ended, z3 on the formula, moved roots, CONFIRM)
   and marks NO-SYMBOL (an UNSAT over nothing that moves).
5. **An unexplained regression gets a read-only diagnosis agent at once**, while the run is still live (it can take
   a stack); the run is stopped once the evidence is taken. Diagnosis and the fix of other classes go on beside it.
6. **One owner per area, many areas at once:** each coding agent keeps one area (COMPOSE, schedule/time, identity,
   driver/SEED, scope) across packages, so independent problems advance together; designs that touch identity, the
   schedule, symbols or soundness are approved first, and a review agent reads such a batch before its merge.

7. **A case's budget is a share of the cluster**: with 20 heads at once a case gets far fewer replay slots than alone;
   HG9's 90-min default cut six cases that closed at 3 h. Give a full sweep `CASE_TIMEOUT_SECONDS=10800`; rerun a cut
   case at once from its jobs-file line (OPERATIONS §4), beside the rest.
8. **Shared services must not have a thundering herd**: the host ledger, NFS directories and `lift11` (the owner's
   machine and the lead's shell) are shared by everything. Offline gates go through `onlift.sh` off lift11, a few cases
   at a time; one shell per host refreshes the ledger's memory reading (b7c5dc99d); every background wait has a
   timeout and an end condition that can happen.
9. **After two large merges, a small live check of their combination** (HG10V: 17897, 11741, 14, 15, 10 from one
   snapshot, one head per host) before the next merge, while agents keep their own gates running.

10. **Reasonable, not maximal** (owner 2026-10-06 afternoon: "你也不要过分并行哈。合理的并行。要不然反而会让速度变慢"): about 8-10
   live campaigns in all, each agent at most 2 at once, critical path first; past that every case slows (2026-10-06:
   ~18 live, 17897 took 4387 s against 578 s) and nothing ends sooner.
11. **Development and final runs overlap; gates that do not depend on each other never queue** (owner 2026-10-06
   evening: "现在你足足有10个liftserver可以并行啊。你就是一起开发这些case，也不至于那么久啊"): the session's last hours
   lost time to a serial chain -- agent gate, review, merge, then a separate final round. What worked instead: merge
   the fixes that already passed their own cases into one integration head and start the final round on it at once
   (HF1), while the next fix is still in development; run a review agent beside the runs, not after them; drop a
   gate on cases another branch already closed; a long case (11741) gets its own run with its own budget as soon as
   its code is final. A run that will certainly fail (07 before its tree workaround) is stopped at once to free its
   slots.

## 4. What does not parallelize, and how it gets faster

- **One seed replay is one JVM**, held to the recorded order. More lifts do not shorten it; replay fidelity does:
  every schedule give-up costs the 15 s watchdog plus a grace (80 give-ups = 20+ min, and every obligation replay cut
  from it inherits the drift). Deterministic listings are speed work as much as correctness work; the start-up/clock
  family's give-ups are handled by workarounds (RULES).
- **SEED's static passes** read the classpath over NFS: Soot's directory lookups made ~200K failed `stat`s per pass;
  `IndexedSourceLocator` lists each looked-up folder once per JVM (~7K left). On warm caches the pass is analysis-bound
  (43-62 s for hdfs-adhoc-19 either way); the many passes per SEED are the cost.
- **Planned:** a SEED shared through NFS, keyed by the tree's commit, the static inputs' digest and the case, so
  repeated runs of one case (agents' probes, validation sweeps) reuse one recording instead of making their own.

## 5. Examples

**2026-10-05 day:**

At one time: the lead's sweep HG7R (15 rerun cases, 2 heads per lift), HG7N (the 10 named bugs, the regression
baseline), HG7D (QJM 08/09 with a 3 h budget); coding agents A1 (COMPOSE cost gate, offline), A2 (time model, up to
four probes), A3 (r4 trees built on two lifts, then four validation runs), D1 (container writers, offline gate then
live), A4 (SEED's static-pass gate); diagnosis agent D2 (the 24/26/37 give-up regression, found in 15 minutes while
the runs were live). Each wrote only its own worktree and `GC_OUT`; the ledger kept every lift under 70 %.

**2026-10-06 (night):** at one time the lead's HG9 (35 non-clock cases, 2 heads per lift) and, after cutting its queue,
HG9B (the 10 named bugs, 3 h budget), six 3 h reruns (HG9L-*) and SW1 (the three swapped-in checks); coding agents A1
((b2) offline gate over 42 corpora + live AR3, then export weave AW4/AW5), A2 (time model probes TM13-TM16), A4 (decider
DO2 + offline A/B), D1 (frontier depth FD2/FD3 + container writers CW5); review agents on the time model, (b2) and the
decider. 14 merges into `system/hdfs` that day, each validated beside the others. The cost of that load: lift11's NFS
jam (fixed) and budget cuts (rerun at 3 h).

## 6. The recipe as run on 2026-10-12 (Solr): copy it

What one lead and four coding agents did to keep ten lifts busy without NFS or the control host becoming the
bottleneck. Every command here is current; the numbers are measured.

**1. The control host (lift11) stays light.** Claude Code sessions -- the lead and every agent -- run on lift11, and
every tool call starts a shell there.
- First thing in a session: make sure no shell carries `BASH_ENV`. The login environment exports
  `BASH_ENV=/sw/ubuntu/custom/lmod/lmod/init/bash` (`/etc/profile.d/modules.sh`), so every non-interactive bash reads
  `/sw`; when `/sw`'s automount hangs on lift11 (2026-10-12: lift11 only, every other lift answered in ms) each
  `bash` waits minutes (`bash -c true`: 30 s+ with it, 6 ms without) and the sessions' shells pile up in D state (60 at
  load 65). No GraphChecker tool needs lmod. Append once per session:
  `printf '\nunset BASH_ENV\n' >> "$(ls -t ~/.claude/shell-snapshots/snapshot-zsh-*.sh | head -1)"`, check with
  `echo ${BASH_ENV:-unset}`; a long-lived shell started before runs `env -u BASH_ENV bash ...`. Put the same line in
  every agent brief.
- Shells already stuck in `autofs_wait` (`cat /proc/<pid>/wchan`) take `kill -9` (the automount wait is killable); kill
  by pid only those older than ~10 min, never by pattern.
- Diagnose before blaming NFS: `timeout 20 stat <path>` for each mount (`/u/vnr3ne`, `/bigtemp`, `/sw`) on the slow host
  and on two others. On 2026-10-12 NFS answered in 2-9 ms from every other lift under ten campaigns; a git checkout
  per lift was not needed.
- Nothing heavy and no polling on lift11: builds, tests and offline gates go through `tools/onlift.sh`, which
  never picks lift11 unless `LIFTS` names it (`tools/pick-lift.sh` drops it from the default list when `LIFTS` is
  unset; 2026-10-13, an `mvn` build landed there with `LIFTS` unset); each agent keeps at most ONE background
  waiter, polling from another lift at >= 60 s; campaigns launched while sessions run on lift11 leave it out of
  `LIFTS` (below).

**2. Launching.** One command per batch of cases; heads are chosen by room, never lift11, every obligation spread over
`LIFTS`, each start to the host with the most room (a replay ended for memory queued again at its full need, never a
verdict; OPTIMIZATIONS 1.32):
```bash
cd ~/gc-run/<snap> && env -u BASH_ENV \
  LIFTS="lift06 lift07 lift08 lift09 lift10 lift12 lift13 lift14 lift15" \
  CASES="solr-18406 solr-18413" CASE_TIMEOUT_SECONDS=10800 PRUNE=0 GC_OUT=/bigtemp/vnr3ne/gc-out/<agent or round> \
  CAUSYNTH_CUSTOM_JDK_HOME=/bigtemp/vnr3ne/vm-force8/j2sdk-image tools/rounds/launch-round.sh ~/gc-run/<snap> <ROUND>
```
`CASE_TIMEOUT_SECONDS`, `PRUNE` and `CAUSYNTH_CAMPAIGN_STOP_AFTER` reach the heads on the command line (ssh carries no
environment). A case that needs another Solr tree: its `case.sh` `repo=` lines edited in the snapshot only, or a
`GC_TREES` directory whose `lucene-solr-checks` links to the tree (`sg3-trees`, `ib-trees`).

The head's own chain is short (OPTIMIZATIONS 1.33): an answer lands as it is collected, a session is gated where its
worker staged it before it lands and the gate reads only the sessions it gates (the ones before by their records), and
GROW's planner and weave build their generation beside the loop -- the pool is never left idle while the head gates,
grows or waits for a step.

A hard question no longer holds its host: every obligation is first asked at 60 s, and an undecided one waits in the
hard lane for z3 alone at the full budget over the query its first ask built, in a JVM that reads no corpus (about
5 GB charged, four to a free lift; PIPELINE §7.5; SP4-10: 12 z3 races of up to 30 min had held every solve slot of
the case; SGF7-adhoc-39: a corpus JVM per hard ask, 18-21 GB, one per host), nor the rounds: a round is planned while
only hard-lane asks run, their obligations in flight, their verdicts landing in the next (SGF8-adhoc-40 round 6 idled
the 13 lifts 12 min behind two; PIPELINE §7.9).  The head starts a round's burst at tens of starts a second, each
host's memory read beside the loop rather than over ssh per start (PIPELINE §7.7; it started one a second, a round 0
of 600 solves and ~500 replays ~18 min of starts).  No question is answered in a corpus
JVM of its own: a cold host's question hands its charge to the solver it starts. A host's solver answers eight questions
at once over its one corpus read (OPTIMIZATIONS 1.34). A question starts a new corpus solver only when none serves
or starts yet, when the queued questions at this campaign's measured seat time would outlast a solver's measured
corpus read on the serving solvers' seats, or when the oldest of them has already waited that long
(`campaign_stream_solver_due`): a big corpus keeps one warm solver and
leaves the other lifts to replays (SGF7-39: 13 to about 121 replays at once). A flip query states only the flipped
condition's independence cone (`FlipQuery#cone`, KLEE constraint independence; PIPELINE §7.5): smaller queries,
and an unrelated undecidable conjunct no longer makes the flip unknown.

**3. Memory, the one limit.** No lift past 70 % (the ledger). Two charge rules keep the ledger close to real use:
- an engine JVM at heap H is charged its footprint H + H/16 + 384 MB (`campaign_jvm_footprint_mb`): charged at H, a
  served planner that filled its heap was ended for 183 MB on a full host and its campaign failed (07, 21);
- a stream replay is charged a quarter more than the seed replay's life's mean until eight returned, then the 90th
  percentile of the returned replays' lives' mean resident memory (rounded up to 128 MB, `campaign_replay_typical`),
  and is counted the cores replays measurably keep busy (`campaign_replay_cores`, 2026-10-17: 05's replays 2.2-3.7
  cores each, counted one); a host admits one only with room for four ends
  of their peaks' 90th percentile less that charge (2026-10-16: replays peak in their last read, publishing; at
  the peaks' 90th percentile a lift's ledger held 19840 MB over 4831 MB of real use), its heap still the largest
  peak times 1.5: charged at the largest, ledgers held 21-22 GB
  over 8-11 GB of real use and no host admitted a start (21: peaks p50 918, p90 1242, max 2234 MB, each charged 3456).
  After both: 18406 757 s (1000-1750 before), migrate 604 s, 18413 PASS, all native 10/10 (round LD2).
- Judge a host by real use and live charges (`$CAUSYNTH_HOST_LEDGER/<lift>/charges/`, mtime < 120 s: their MB and
  cores), and its load against its charged cores.

**4. Agents and trees.** At most five coding agents (owner 2026-10-18; four before), each with its own branch, worktree (`tools/lib/worktree-add.sh`,
a sha), frozen snapshots `~/gc-run/<prefix><n>`, `GC_OUT` and at most two live runs; read-only reviewers beside the
runs, not after them. Each Solr tree has ONE owner who builds it; anyone else only reads it. Before any build: `pgrep
-fc '[l]ucene-solr-<name>'` on every lift. When a tree is read by others' runs and needs a change, build a second
tree (a new worktree and branch) and point the new runs at it rather than waiting for a quiet window. Agents cannot
message each other by name: the lead relays.

**5. Watching without polling the control host.** One Monitor per session, its loop on another lift:
```bash
ssh lift06 env -u BASH_ENV bash /bigtemp/vnr3ne/analysis/solr-2026-10-12/watch-remote.sh \
  /bigtemp/vnr3ne/analysis/solr-2026-10-12/live.txt solr-explore2 solr-zk2 system/solr
```
(every 60 s: a run of the list -- one `accept-*` directory per line -- once its verdict row is written, and each
branch head that moved; as a Monitor's command it notifies the session per event, re-armed every 30 min). Agents report at their
gates; at every check-in compare each agent's last commit time and newest run (AGENTS.md: an agent listed as running
may be idle).

## 7. 2026-10-18: what changed

- The head's memory is no longer the limit: compaction (OPTIMIZATIONS 1.26, 1.28-1.30) and the holding composer (1.27)
  keep the planner at ~3.5 GB and the composer at ~1.9 GB on 05 r5 / 07, so session sharding of the planner is shelved
  (branches solr-parplan 3df494a3a, solr-shard d3b663462 kept, not merged).
- Measured on 07 (idle-pool/): the pool idles because of the head's serial chain (landing, the import gate, GROW in
  the head's hands, one solver at a time) and a dispatch cursor that piles replays on one host -- not capacity; the
  scheduler rewrite (branch solr-stream2) addresses each. During a final round, agents keep off the pool.

## 8. CloudLab: five big-memory nodes, filled by their cores (2026-10-25)

The owner, 2026-10-25: "我们的cloudlab一般是5个节点，是大内存。这点和之前的liftlab不同。所以在system/hdfs-cloudlab和
system/zookeeper-cloudlab上，我们的并行策略要最大化cloudlab集群的使用。" The two clusters bind on different resources:

| | liftlab (lift02-15) | CloudLab (node0-4) |
| --- | --- | --- |
| hosts x cores x memory | 14 x 48 x 30 GB: 672 cores, 420 GB | 5 x 40 x 251 GB: 200 cores, 1255 GB |
| replays a host holds (4-8 GB, 1-2 cores each) | 3-5, by memory (70 % of 30 GB) | 20-40 by cores, 20-40 by memory |
| what binds a round | memory | cores |
| a case over 30 min | ran again alone on all 14 lifts, to have their memory | runs beside every other case: no node's memory fills |

So the strategy on both CloudLab branches is to keep every core charged with useful work and to charge cores as they are
used:
1. **Hundredths of a core.** The ledger charges a replay its measured mean cores (`workload_cores_x100` over the
   replays it returned, recomputed every eight; the seed's own before that; at least 0.10), a solver 2.00, an engine JVM
   1.00, a native run 1.00, a fan-out job 1.00, all in hundredths (`<mb>.<cores x 100>.<host>...`). The liftlab rule, the
   90th percentile rounded up to whole cores, cost nothing where memory bound first; on CloudLab it left a third of the
   CPUs idle: HDFS's final series' 768 replays averaged 1.63 cores (p50 1.50, p90 2.46) and were charged 2 or 3, so a
   node showed 40 cores charged under a load of 25-55. With 20-40 replays on a node their sum is their mean times their
   number, so the mean is the charge. Where charges still overstate the cores, the load decides: a resident solver
   keeps the 2.00 cores of the solve it took over for its life, idle, and each seated question charges 2.00 more, so
   with 14 ZooKeeper and 9 HDFS campaigns at once (rounds Z1 and P1) node1 read 40 cores charged under a load of 13-16,
   77 % idle. Cores oversubscribe gracefully where memory does not, so admission and every host order count a node
   busy as the lesser of its charged cores and its load plus the cores charged in the last 120 s, which the 1-minute
   load has not caught up with (`campaign_host_busy_cores`; the memory reading carries `/proc/loadavg`). A build
   before it writes readings without the load, so while one runs beside it the charges stand.
2. **One pool per round.** `tools/rounds/run-pool.sh <round> <cases.tsv> <branch>=<snapshot>... [case...]` replaces
   fixed lanes and the alone reruns: it starts the case with the longest expected wall first (`POOL_EXPECTED`, rows
   `case<TAB>seconds`, e.g. the results table's wall column; else the case budget), whenever 10 % of the cluster's cores
   are free both by the ledger and by `/proc/loadavg` (`POOL_FREE_CORES`, hundredths), at least `POOL_GAP_S` (30 s) after
   the last start (`POOL_MAX` caps the cases at once; 0, none), its head on the node heading the fewest of the pool's
   cases (ties: the most free cores, then memory room). A case's obligations still go to every node (level 1). A
   case's pool run is its record. `series-<round>.log` has START/END rows as `run-series.sh` writes them, and
   `pool-<round>.tsv` a row per poll: time, cases running, the cluster's free cores, and per node load, free cores
   (hundredths) and memory room (MB). Stop starting new cases: `touch $GC_OUT/series-<round>.STOP`. Run the pool from
   a snapshot, not a worktree you edit: bash reads its script as it runs.
3. **Memory is spent, not rationed.** Heads keep their heaps for life and nothing else changes: a round of every case
   at once stays far under a node's 70 % ceiling (175 GB), so the only memory rule left is the ledger's.

4. **Measured (2026-10-25, ZooKeeper rounds Z1-Z5 beside the HDFS named cases' pools P1-P4).** The ledger's steps cut
   the nine HDFS named cases' summed walls from 15710 s (P1, whole cores by the mean, the pool gating by charges
   alone) to 10099 s (P3, the load and a start's decayed cores), 9 of 9 PASS, beside 16 ZooKeeper cases at once; the
   final series ran the same nine in 9472 s on fewer campaigns. Z4's whole round of 16 cases, 13 of them in 58
   minutes, kept 54-59 % of the 200 logical CPUs busy (`/proc/stat`, `cpu-Z4.txt`): a node's 40 logical cores are 20
   physical ones, so that is the physical cores full. Admitting by idle logical CPUs instead (Z5, P4: the busy cores
   from `/proc/stat`) packed more replays, kept the CPUs no busier and ran 11 of 12 ZooKeeper cases 1-25 % slower and
   the HDFS nine in 13376 s, so it was reverted: on these nodes the physical cores bind, and the load (which counts a
   thread waiting for one) is the better gauge.