# Lessons: the traps we fell into, how we measure, how we debug (2026-10-18)

Read after RULES.md, AGENTS.md, OPERATIONS.md, PARALLEL.md, CHECKING.md and REFACTOR-PLAN.md. Every item below
cost us time at least once; the date or the case it came from is named so it can be checked.

## 1. How we work (pointers; the rules themselves are in RULES.md)

- A small workaround beats a huge engine change ("如果一个workaroud能解决一个巨大的工程改动，就是可以的"), but
  the design stays general; every workaround is named in STATUS (RULES.md "Workarounds, with measure").
- One implementation per concept; what a change replaces is deleted -- no flags, no fallbacks, no old path kept
  "for comparison" (owner 2026-10-18: "旧的代码就要全部删除了。再也不用了"). Comparisons use old run
  OUTPUTS and old snapshot jars, never old code in the tree.
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
- Heredocs: a heredoc inside a python heredoc needs a distinct delimiter (`<<'PYEOF'`); a python text holding a
  line `EOF` ends a shell `<<'EOF'` early (2026-10-19): write such scripts to a file and run the file.
- The tool's safety check refuses `rm -rf $VAR/...` with an unquoted variable, and the call waits instead of
  failing: an analyst agent sat 2 h on one (2026-10-19). Use literal absolute paths or `"${VAR:?}"/...`.
- Start a detached remote driver with `ssh -f host 'setsid nohup ... &'`: without `-f` the local ssh waits on
  the remote's output forever.
- `tools/onlift.sh` passes no environment to the remote command: `HBASE_MAVEN_REPO=x tools/onlift.sh ... build.sh` built
  into build.sh's default repository, another agent's at the time (2026-10-19, agent H2). Put variables inside the
  command (`tools/onlift.sh -h <host> env NAME=value ...`); `experiments/hbase/build.sh`'s default repository is now
  named by the tree's path, so a lost variable builds into a repository of that tree's own.
- Never source run_engine.sh functions through process substitution in a foreground call
  (`bash -c 'source <(sed -n ... run_engine.sh)'`): an agent hung 3 h on that (2026-10-18). Extract the
  functions to a file, run with `timeout`.
- Every wait is an `until` loop with a timeout AND a check that its producer is alive; a run that died never
  writes its `exit=` line, and a waiter on it waits forever (several stale waiters were found on 2026-10-17/18).
- Drivers (final-seq*.sh) run detached (`setsid nohup`) on a pool lift, never on lift11. Before repointing a
  driver, read the round log's tail: a case was launched twice once (SGF8DUP).
- A driver's defaults must name the current image and trees: a relaunch without `VM_IMAGE` fell back to
  vm-force8 and two cases died at their seed replay (SGF9VM8-adhoc-39/38). Check the `.job` file of the first case
  after every relaunch.
- Never `git add -A`; never rebuild a snapshot (`~/gc-run/sgf*`) a run reads; worktree creation over NFS can take
  more than 2 min (run it in the background).

- HBase with no WAL (owner 2026-10-19): a master's local region keeps its procedures only in memory until a flush,
  so a standby master that takes over as soon as the active one's znode goes loads the region while the old master is
  still flushing it and misses procedures (agent H2, master-active-time). A workload that restarts a master runs one
  master, stops it cleanly, joins its thread, then starts the next.

## 3. Zombies, orphans, hung agents

- Orphaned z3 (`z3 -in -smt2`, parent init, hours old, 2-3 GB each): kill by pid; z3 must die with its JVM.
- JVMs of a finished case left on a host, ledger charges of a dead service (`.taken`): Service#retire, stop-run.sh.
- Zombies on lift11 belonging to another Claude session (a 2-day-old `claude` parent) are not ours: leave them.
- A subagent with no file activity for > 30 min may be hung inside a tool call: TaskStop it and resume it with
  SendMessage (it keeps its context).
- The watchdog /bigtemp/vnr3ne/analysis/solr-2026-10-18/watchdog.sh (+ watch-remote.sh) runs during rounds and
  exits at the first D-state pid seen twice, ssh refused twice, a stalled case log (> 15 min), a host past 90 %
  memory, a JVM/z3 of a case other than the running one, or a z3 orphaned > 60 min. Re-arm it after each alarm.
  Its stall check must look at every log a case writes, not the case log alone: COMPOSE writes only its
  `placed.*/stderr.log` or `final/compose.log` (SGF9-adhoc-40, -05), a last GROW re-run only its `replay.log`
  (SGF9-adhoc-05, 25 min); all raised false stalls (`analysis/solr-2026-10-18/final9/watchdog9p.sh` now lists all of them).

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
  COMPOSE's hold (RowHold, 60 % of the old generation) does exactly that now.
- Never charge a JDK 8 JVM by its live set: ParallelGC grows the resident set toward -Xmx whatever the live set
  and seldom gives it back. OPTIMIZATIONS 1.36 charged the served planner its measured need (4995 MB); in
  SGF9-adhoc-31 it reached 20220 MB resident at 6.4 GB live beside replays, its growth was refused at 88 % and
  the watcher killed it (EXPLORE lost at round 26). Reverted (19fe33ff0): a long-lived JVM is charged its heap's
  footprint for its life.
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
  before/after numbers on the same inputs. Byte-identity is no longer a gate (owner 2026-10-18 evening): the bar
  is a `.smt` with the right causal chain and a SAT that replays; the old references (planner 05 r5, 05 r2, 13 r10,
  19 r10, 21 r13 in analysis/solr-2026-10-17/nfs/; composer 13, 39, 21, 10) remain a diagnostic.
- Reconstruct timelines from file mtimes (worker dirs: host.txt dispatched, replay_verdict end; planning-NNNN
  dirs; logs), per minute, and attribute idle time to causes in obligation-minutes
  (analysis/solr-2026-10-18/idle-pool/). An idle pool is usually a serial chain on the head (landing, gate,
  GROW, solver queue), not capacity.
- Look at the critical path, not summed thread time. In a distributed design, count bytes on the wire: the
  sharded walk sent 45 GB per walk because shared payloads were repeated per row.
- Decompose a "slow round" before blaming the planner: 05's "70-min round 5" was 15 min of planning and 56 min
  of GROW waiting (2026-10-17, my error, corrected).
- Structural waste is found by asking what each result fed, through every reader: at world depth 0 no GROW re-run
  (36 % of 07's replay time, analysis/solr-2026-10-18/obligation-redundancy/) parents an obligation, yet its session
  is what the closure grows from (§8; SGF8-adhoc-39: 77 obligations, 48 paths came after its re-runs landed).

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
- A speed rule that ends exploration must be argued against every reader of the sessions it skips: the closure
  reads them all. The fixed point beside GROW re-runs (OPTIMIZATIONS 1.37, reverted 2026-10-19) skipped re-runs no
  obligation could be cut from, but the closure's tasks in the regions they wove existed only once they landed
  (SGF9-adhoc-39: 8 paths where SGF8 composed 57; all 7 SGF9 cases it ended left sessions no round planned over).

## 9. HBase (2026-10-19: what moving the engine to a new system taught us)

Order of work that paid off on HBase: make every run identical first (names, placement, periodic work), then
widen what the engine can see, then debug cases one by one, reading each claim's chain before trusting it.

**Make a run repeatable before debugging anything.** Each item was found as a seed replay or a CONFIRM that diverged
from its recording; each is now a tree workaround named in STATUS "Per-system surface".
- Run constants: host name `localhost`, ports in creation order, start codes `1700000000000 + 1000 x order` (R3-10:
  meta on rs1 in the recording, rs0 in the replay; start codes are the run's constants, so a check that needs a
  restarted server's new start code needs a workload that restarts one -- hbase-adhoc-31).
- One master at a time (the first alone, a standby once it is active); region servers report for duty in order and
  the balancer's destinations are sorted, so hbase:meta is on `auto0/rs0` in every run (HZ9-24, HZ12-24: fixed twice,
  4d3cc2d197 then c246d3fe1c -- ordering only the registrations was not enough).
- Periodic work a 30 s recording never reaches and a 10x slower replay does: the WAL roller (a disabled WAL never
  clears a roll request and the roller spins, HZ6-24), periodic memstore flushes, and the master's chores --
  balancer, catalog janitor, cleaners, normalizer, hbck, replication statistics, a system table's fixed 5-minute flush
  (HZ17-24: the balancer moved regions 8 minutes into the seed replay, one close stayed CLOSING, the test's put retried
  without end). All are `NEVER_MS` in automatic mode (tree f9340f2aab). When a seed replay stalls, grep its
  `replay.log` for chore names first. Consequence: a check whose race partner IS a chore (13: CatalogJanitor's GC;
  04: the quota observer) must drive that chore from its workload.
- Procedure steps: each push hands off through `CausynthStep` (START at a do-nothing executor, so a step is a
  HANDOFF_TASK), and the next step is handed off INSIDE the claimed step, not in its `finally` (464505d240: from the
  finally it captured the worker's poll WAKE, and steps' occurrences drifted between runs).
- Async continuations (`CompletableFuture` listeners) stand at their registrant's address wherever they run
  (`Continuations#carry`; review-cont found two HIGH defects before merge). A chain that re-registers per poll nests
  one frame per poll (TODO HBase 8): make that operation a synchronous call in the workload (21).
- Netty: one event loop group per node; a timer task is a lineage start.

**An UNSAT is not a result until `tools/analysis/vacuity.py` says it is not vacuous.** At 19:30 every HBase UNSAT
so far was vacuous: fatal arms literal false (37, 13), map reads at INITIAL with no writer (34, 08, 22, nsrg), writers
dropped as same-thread (15), INITIAL plus BLOCKING (31). Run it on every UNSAT before writing a STATUS row.

**A SAT that "moves nothing" is a faithfulness hole, not a schedule problem.** When CONFIRM refutes on ORDER or
WIRE edges, read the claim's `movedRoots` first. `{}` on the seed path (fatalObserved false) means a symbol in the
fatal's cone is neither pinned nor a root: an unplaced clock cell (#11 HZ17-mat: master0's activation T0, read only
in re-runs on another node; fixed 208ac1899, placement by any node of the same JVM clock), or an `unsupported__` leaf
for an unmodelled operation (HP8-15: `String.equals` of an enum read the lowering stated at REF; fixed: an enum read
that does not move is its writer's name, and a fatal arm the recording did not take is held where nothing it rests on moved).

**A workaround can remove what another fix needs.** Removing `masterSystemTime` from OpenRegionRequest (a clock
export with no mint row) also removed master0's only clock readings from the seed, which left T0 unplaced (H2).
After a workaround, rerun the cases it touches and look for new `DECLARATION_MISSING` / unplaced gaps.

**Read the chain of a SAT before trusting it.** HC14's ns-rsgroup claims rode a CreateTable retry fault and the
startup worker, not the namespace check; the check itself compares an untracked `String` over a `TreeMap`, which no
world can flip. Concrete-by-construction checks (an untracked compare, data through a region's store: 13's meta
cells) are vacuous until a workaround gives them a value the engine tracks (nsrg: a per-group count, 985a0dfe91).

**Target selectors.** A region whose method is called only from another region's body is folded into it: 31's
`throwOnWrongStartCode(long)` never had an occurrence (SEED: DECLARED_TARGET_OCCURRENCE_UNOBSERVED); name the
enclosing region's occurrence. Check the seed's observed occurrences before a long run.

**Fault kinds multiply replays.** 10 queued 210 `HBASE_RPC` REQUEST faults (70 client calls x IOException,
ConnectionClosedException, CallQueueTooBigException), ~10 min of replay each; that, not the 241 refused arms (seconds
each, decided on the worker), was why it did not converge. Compare a fault kind to the run with NO fault: CQTBE is
rejected before it runs and retried on the same cached location = the recording plus time (cut, H3); a
ConnectionClosedException clears the master stub cache and the registry's endpoints (kept).

**One counterfactual per bug is not required** (RULES): HBASE-30484's workload drives the quota observer twice with
`hbase.client.retries.number=0`, so one lost enable is one fault at depth 0; otherwise raise that case's depth.

**Cluster use.** A planner head is charged its full heap for life (OPTIMIZATIONS 1.36): 23.2 GB on a 30 GB host
whose cap is 22.1 GB, so no replay ran beside it, while HBase's engine JVMs peaked at ~3 GB (9.6 GB at most): size
`engine_memory_mb` from the system's measured `engine_peak_mb` files (HBase: 12288 since 2026-10-20). Two heads on a 3-host group left one replay host and R17-10
starved for an hour. Replays use all 14 hosts (`CAUSYNTH_CAMPAIGN_WORKER_HOSTS`), heads stay on the agent's own
hosts (at most 2-3), detached in their own session: heads run from one shell on lift11 were all TERMed when another
round's stop ended that shell's ssh clients (HZ14: 24 exit-255 kills; killed replays are now re-queued, at most twice).
Concurrent `git worktree add` races on `.git/config`: take `/localtmp/vnr3ne/worktree-add.lock` (flock).
