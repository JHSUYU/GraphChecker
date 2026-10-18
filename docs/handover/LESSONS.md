# Lessons: the traps we fell into, how we measure, how we debug (2026-10-18)

Read after RULES.md, AGENTS.md, OPERATIONS.md, PARALLEL.md, CHECKING.md and REFACTOR-PLAN.md. Every item below
cost us time at least once; the date or the case it came from is named so it can be checked.

## 1. How we work (pointers; the rules themselves are in RULES.md)

- A small workaround beats a huge engine change ("如果一个workaroud能解决一个巨大的工程改动，就是可以的"), but
  the design stays general; every workaround is named in STATUS (RULES.md "Workarounds, with measure").
- One implementation per concept; what a change replaces is deleted -- no flags, no fallbacks, no old path kept
  "for comparison" (owner 2026-10-18: "旧的代码就要全部删除了。再也不用了"). References for byte-identity are
  old run OUTPUTS and old snapshot jars, never old code in the tree.
- Read the existing mechanism before adding one (owner 2026-10-18: "不要重复造轮子"). Example: the arm key
  (ObligationFactory#dependence) already was a KLEE-style independence slice; the depth-1 explosion came from
  Corpus#inputShape naming handoffs by every varying root (Arms rootGuards), and a fix was parked on branch
  solr-armkey -- found only by reading the code and git log, not by literature.
- Decide engineering questions yourself and report; ask the owner only about his own rules (e.g. rerunning a
  case that has a result, the world depth he controls).
- At most 5 coding agents (owner 2026-10-18); one branch and worktree each; give each agent its own hosts; the lead merges;
  one review at complex places (concurrency, schedule, soundness). Both reviews of 2026-10-17/18 found real bugs
  (a JDK 8 HashMap race; a witness that could be swapped out).

## 2. Shell and process traps

- Always `env -u BASH_ENV` for builds, runs and ssh: BASH_ENV=/sw on lift11 jammed shells on an autofs hang
  (~1 h lost, 2026-10-12).
- `pgrep -f pattern` matches the shell running it (and an ssh `bash -c` carrying the pattern). Use
  `grep '[p]attern'`, compare pids, and kill only by explicit pid. Stop a run with tools/rounds/stop-run.sh
  (process groups on every lift), never pkill.
- zsh is the login shell: `====` is `=command` expansion ("=== not found"); an unmatched glob is an error
  ("no matches found"); quote globs or test with `ls -d` first.
- Heredocs: a heredoc inside a python heredoc needs a distinct delimiter (`<<'PYEOF'`).
- Never source run_engine.sh functions through process substitution in a foreground call
  (`bash -c 'source <(sed -n ... run_engine.sh)'`): an agent hung 3 h on that (2026-10-18). Extract the
  functions to a file, run with `timeout`.
- Every wait is an `until` loop with a timeout AND a check that its producer is alive; a run that died never
  writes its `exit=` line, and a waiter on it waits forever (several stale waiters were found on 2026-10-17/18).
- Drivers (final-seq*.sh) run detached (`setsid nohup`) on a pool lift, never on lift11. Before repointing a
  driver, read the round log's tail: a case was launched twice once (SGF8DUP).
- Never `git add -A`; never rebuild a snapshot (`~/gc-run/sgf*`) a run reads; worktree creation over NFS can take
  more than 2 min (run it in the background).

## 3. Zombies, orphans, hung agents

- Orphaned z3 (`z3 -in -smt2`, parent init, hours old, 2-3 GB each): kill by pid; z3 must die with its JVM.
- JVMs of a finished case left on a host, ledger charges of a dead service (`.taken`): Service#retire, stop-run.sh.
- Zombies on lift11 belonging to another Claude session (a 2-day-old `claude` parent) are not ours: leave them.
- A subagent with no file activity for > 30 min may be hung inside a tool call: TaskStop it and resume it with
  SendMessage (it keeps its context).
- The watchdog /bigtemp/vnr3ne/analysis/solr-2026-10-18/watchdog.sh (+ watch-remote.sh) runs during rounds and
  exits at the first D-state pid seen twice, ssh refused twice, a stalled case log (> 15 min), a host past 90 %
  memory, a JVM/z3 of a case other than the running one, or a z3 orphaned > 60 min. Re-arm it after each alarm.

## 4. NFS and storage

- /bigtemp is corezfs04, a shared department ZFS over NFS v3; every lift has 1 Gb/s (~115 MB/s). Under our own
  load a 164 MB read ran at 19 MB/s. Session rows are therefore `.jsonl.gz` (gzip level 6, sync-flushed appends,
  17-27x smaller), read through one opener (smt.ArtifactIO#input; shell `campaign_rows`). Old plain run dirs are
  NOT readable by the new code: make a compressed copy with analysis/solr-2026-10-17/nfs/tool/GzCopy (it never
  writes into its source).
- NFS attribute caching: a file created on one host is seen on another ~29 s later; a stat of a missing file
  can stay cached "absent" for 30-60 s. So create files before any reader starts, open instead of stat
  (close-to-open consistency), and use an append-only journal instead of a directory listing for state other
  hosts must see (withdrawn.txt for GROW swaps). A file protocol between hosts is too slow: use TCP.
- D-state processes are NFS hangs: look at every check-in. Moving many files serially is slow (a GROW swap was
  ~9.6 s): batch them.
- Home quota 100 GB: bulky data on /bigtemp/vnr3ne, per-lift scratch on /localtmp/vnr3ne. Delete heap dumps
  (tens of GB) as soon as the before/after is measured.
- lift15 refused ssh public keys for ~2 h (its /u autofs); ssh under many parallel connections can fail with
  "kex_exchange_identification: Connection closed" (sshd MaxStartups): retry, bound the fan-out.

## 5. Memory and heaps

- Size a heap with run_engine's own functions (`campaign_jvm_footprint_mb` + the composer's z3 room against
  `campaign_host_limit_mb` minus the lifts' real in-use) -- never by hand: three hand-sized heaps (20000, 18432,
  24576) made a head step wait forever.
- Never predict a JVM's memory from file sizes: the planner held 0.32-0.37x of its session files as rows but
  peaked at 0.57x to >1.09x (40's Frontier). Measure the old generation after a full collection (HeapWatch);
  the planner's hold rule does exactly that now.
- A heap basis that follows the largest peak ever seen (2048 -> 9728 MB in 07) shrinks every host's room.
- Before an architecture change for memory, take a heap dump and attribute it by owner
  (analysis/solr-2026-10-18/redundancy/tool/HeapOwners.java): 68 % of the planner's 12.7 GB was redundancy
  (unread gap text, strings with embedded session ids, string sets), so compaction (12.7 -> 4.0 GB) replaced
  the planned session sharding.

## 6. Concurrency traps (Java 8)

- HashMap.computeIfAbsent of a PRESENT key resizes after a threshold-crossing insert: a "read-only after
  pre-indexing" HashMap shared across threads is a race. Build shared maps on one thread and only get() them,
  or use concurrent maps; assert the builder thread.
- invokeAll returns at the first exception while other parts run: wait for all parts.
- A step computed ahead must be re-walked in order when its input changed; count a task as running only after
  the pool accepted it (else drain() waits forever).
- Background writers must be joined before anything takes the file's mtime as a metric.
- JFR on JDK 8 misattributes inlined frames (HashMap$TreeNode.getTreeNode looked hot; real symbols had zero hash
  collisions): confirm a hot spot by timing or counting before acting.

## 7. Measuring performance

- Measure first, prove the mechanism, then fix (two GC-flag "fixes" failed on 2026-10-16). Every fix lands with
  before/after numbers on the same inputs, and outputs byte-identical where semantics do not change: planner
  references 05 r5, 05 r2, 13 r10, 19 r10, 21 r13 (compressed in analysis/solr-2026-10-17/nfs/), composer
  13, 39, 21, 10.
- Reconstruct timelines from file mtimes (worker dirs: host.txt dispatched, replay_verdict end; planning-NNNN
  dirs; logs), per minute, and attribute idle time to causes in obligation-minutes
  (analysis/solr-2026-10-18/idle-pool/). An idle pool is usually a serial chain on the head (landing, gate,
  GROW, solver queue), not capacity.
- Look at the critical path, not summed thread time. In a distributed design, count bytes on the wire: the
  sharded walk sent 45 GB per walk because shared payloads were repeated per row.
- Decompose a "slow round" before blaming the planner: 05's "70-min round 5" was 15 min of planning and 56 min
  of GROW waiting (2026-10-17, my error, corrected).
- Structural waste is found by asking what each result fed: at world depth 0 every useful verdict came from
  round 0, and GROW re-runs (36 % of replay time) could not feed exploration
  (analysis/solr-2026-10-18/obligation-redundancy/).

## 8. Debugging and verification

- A run that looks wrong is stopped and debugged at once; slow means a defect somewhere.
- Canary a change on a small case alone (solr-adhoc-13) before a round; compare its claim and stage times with
  the last good run.
- z3 is nondeterministic under resource limits: the same self-check hits the 60 s wall or the 960 MB memout on
  different runs; compare candidate.smt2 bytes, not undecided self-check texts.
- Correctness of schedule changes is argued invariant by invariant (a confirmation's corpus, a solve's corpus,
  the witness of an attempt, an obligation never run twice) and each gets a table test.
- Dedup only what is provably equivalent (completeness > precision): node/window-symmetric flips looked alike
  but 224 of 309 brought new demand. Over-approximate in COMPOSE (havoc), confirm strictly.
- Early-stopping replays is unsafe in general: under "no recorded-order pruning" the closure keeps reading rows
  until the test method ends; only the window close is a safe stop.
