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
| across development | up to 4 coding agents, read-only diagnosis and review agents, the lead's rounds | each agent on its own branch, worktree, snapshot and `GC_OUT`, up to four live runs at once; offline gates and builds via `onlift.sh` on the least loaded lift ([AGENTS.md](AGENTS.md)) |

The only limit is memory: no lift above 70 % (the ledger refuses a start past it, a running JVM past it is ended).
Cores and load are not limits: 48 per lift.

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
- **Host-dependent state is a hazard:** what differs between lifts or file systems (a directory's listing order, a
  temp path, a host name) makes a recording on one host and its replay on another disagree. The engine fixes such
  orders in both passes (random draws: `runtime/Randoms`; directory listings: branch `hdfs-sorted-listings`, in
  validation), never by pinning work to one host.

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

## 4. What does not parallelize, and how it gets faster

- **One seed replay is one JVM**, held to the recorded order. More lifts do not shorten it; replay fidelity does:
  every schedule give-up costs the 15 s watchdog plus a grace (80 give-ups = 20+ min, and every obligation replay cut
  from it inherits the drift). The time model and deterministic listings are speed work as much as correctness work.
- **SEED's static passes** read the classpath over NFS: Soot's directory lookups made ~200K failed `stat`s per pass;
  `IndexedSourceLocator` lists each looked-up folder once per JVM (~7K left). On warm caches the pass is analysis-bound
  (43-62 s for hdfs-adhoc-19 either way); the many passes per SEED are the cost.
- **Planned:** a SEED shared through NFS, keyed by the tree's commit, the static inputs' digest and the case, so
  repeated runs of one case (agents' probes, validation sweeps) reuse one recording instead of making their own.

## 5. An example (2026-10-05 day)

At one time: the lead's sweep HG7R (15 rerun cases, 2 heads per lift), HG7N (the 10 named bugs, the regression
baseline), HG7D (QJM 08/09 with a 3 h budget); coding agents A1 (COMPOSE cost gate, offline), A2 (time model, up to
four probes), A3 (r4 trees built on two lifts, then four validation runs), D1 (container writers, offline gate then
live), A4 (SEED's static-pass gate); diagnosis agent D2 (the 24/26/37 give-up regression, found in 15 minutes while
the runs were live). Each wrote only its own worktree and `GC_OUT`; the ledger kept every lift under 70 %.
