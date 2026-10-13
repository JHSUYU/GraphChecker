# Performance: where a campaign's time goes, how the cluster runs many at once, and how to debug a slow case

The owner's rules ([../handover/RULES.md](../handover/RULES.md)): every case should be fast (tens of minutes); a case
far slower than its peers or its history is investigated at once, never waited out (a long run usually hides a
correctness defect); time optimization never ends; every speedup is general, never per case; a genuinely large closure
gets resources (the whole cluster), never a cut. This document is the design of the speed side, the pitfalls that cost
the most hours, and the debugging method. The pool's mechanics in full are PIPELINE §7.7; this is the map.

## 1. Where a campaign's time goes

A campaign is one head process (`run_engine.sh`) that drives the stages; every heavy step is a JVM or a replay that the
head places on some lift. Typical numbers (2026-10-05, sweeps of the HDFS group at 2 heads per lift; a case run alone
on the cluster is faster):

| stage | what costs | typical | what made it slow before |
| --- | --- | --- | --- |
| SEED | 2-7 Soot static passes (a fresh JVM each: again when the demanded doors grow, again after each scope growth), the recording on stock JDK 8, the trace aggregation | 3-9 min | Soot's per-directory class lookups on NFS: one pass made ~232K file syscalls, ~197K of them failed `stat`s on the classpath directories; a burst of 20 heads starting together tripled pass times (HG5A first wave: passes 60-308 s against 13-90 s later). `IndexedSourceLocator` lists each looked-up folder once per JVM and the pass's JVM runs on the jar alone: hdfs-adhoc-19 ~41K file syscalls per pass, ~7K failed stats; a warm pass is unchanged (43-62 s, lookups were 3-25 % of it, now 0-4 %); the first wave's cold cost is not measured again |
| INSTRUMENT | weaving (Soot) and the JVM verifier | 1-2 min | same NFS lookups (fixed with SEED's) |
| REPLAY (seed) | one concolic replay of the workload on the Zero VM, held to the recorded schedule | 2-8 min; every schedule give-up costs the 15 s watchdog | replays that depart from the recording's order (the start-up/clock family: 30-170 give-ups); the budget's reserve then owes twice the seed replay's time (§3) |
| EXPLORE | planner rounds (one JVM each), obligation SOLVEs (z3 on a host's warm solver), obligation REPLAYs (~1-4 min each), GROW re-runs | 5-60 min | queue waits on an over-charged ledger (§3); closures of many equivalent occurrences; re-asked arms |
| COMPOSE | the corpus read, one formula over every admitted session, z3 per valuation | seconds to minutes (hdfs-adhoc-07's 556 sessions: 2-3 min offline, most of it the read) | the self-check searched the 26 MB body per command and path: 07 did not finish in 17 min (HR1) |
| CONFIRM, EMIT, REPRODUCE | one replay of the witness world; artifacts; N native runs | 1-10 min | a remote CONFIRM's path bug lost results (fixed 71df98a00); EMIT up to 233 s on a large corpus |

Measured per campaign in `out/<case>/schedule/stage_metrics.tsv`; `tools/analysis/timeline.py <case dir>` splits it by
stage, round and job (streaming layout; the per-round solve/replay waits included).

## 2. How ten lifts run many campaigns at once (the design)

Ten lifts (`lift06`-`lift15`), 48 cores and 30 GB each, NFS-shared home and `/bigtemp`. Everything is placed by
memory, through one ledger, so any number of campaigns, gates and agent runs can share the cluster without a host
running out of memory, and a single case alone takes the whole cluster.

- **The host ledger** (`$CAUSYNTH_HOST_LEDGER/<host>/charges/`, PIPELINE §7.7): every start (a replay, a solve, an
  engine JVM, a recording, a gate JVM, a `fanout.sh` job) is first charged on its host. A start goes only when both
  the host's live charges and its real use (`MemTotal - MemAvailable`), plus the start and any head's held room, stay
  within 70 % of `MemTotal`. A charge is a file whose mtime is a 120 s lease renewed every 10 s by its holder, so a
  killed run's charges lapse; it is removed the moment what it ran returns. A running JVM that outgrows its charge asks
  for the excess and gets it unless the host's REAL use would pass the ceiling.
- **Measured charges** (2026-10-05): a replay is charged the campaign's measured replay need (the largest resident
  peak its replays stated so far x1.5, at least 512 MB); only the seed replay, before anything is measured, is charged
  twice the recording's measured peak at its start (its heap sized for seven times it; capped at half a host), and
  grows past that while its host has real room: charged seven times, four HI2 seed replays held 44 GB of the ledger
  over less than 4 GB of real use (HDFS seed replays peak at 0.5-1.4 times their recording). Obligation replays peak within +-10 % of their own
  seed replay (HG4: 11741 674 / 662-715 MB; adhoc-07 238 / 194-257; outlier adhoc-15 514 / up to 2003, which grows
  through the ledger).
- **An obligation is two starts**: its SOLVE (on a host where its campaign's solver serves, charged its question's z3 run,
  `campaign_question_mb` 512 MB: z3 runs measured a median 1 MB, p90 369 MB, at most 1.8 GB over 118 processes, while
  1 GB each held 51 GB of the ledger in HI2; on a cold host what a solver starts at, 1 GB) and, only when the solver answers SAT_MODEL_READY, its REPLAY, queued behind the solves
  (a witness's confirmation and GROW's re-runs lead the queue; the solves follow, since a solve takes seconds and
  decides whether a replay is owed: solr-adhoc-21 RX4 left 1075 of 1158 in flight as solves never started behind
  replays), on the class tree and plan its solve started on.  Dispatch starts the first entry a host admits (a replay
  no host has room for holds no solve); an entry queued past `campaign_stream_wait_bound_s` (600 s) goes first and
  alone, so a stream of solves never starves a replay. Until the replay lands the obligation is in flight (never re-proposed). Most
  obligations end at the solve (UNSAT, refused), so they never wait for replay memory.
- **The shared pool** (a sweep, `stream_shared_pool=true`): the explorations running at once divide the pool's slots
  (as many replays as fit under the ceiling at the measured charge, at most the cores, per host) by the number of
  explorations whose entry in `$CAUSYNTH_HOST_LEDGER/explorations/` is fresh, re-read at every start. One case alone
  keeps all of it; ten keep a tenth each, and a share grows as others end. A named acceptance run shares nothing.
- **Head steps** (PIPELINE §7.7 HEAD STEPS): every engine JVM of a head (static passes, planner, composer, CONFIRM's
  main, GROW's planner) goes to the head's own host if it fits, else to the pool's host with the most room, charged
  at the heap it starts at; a step that waits holds its need on the best host so that host drains. A head holds room
  for its next step: its measured step need (the largest engine JVM peak x1.25, at least 1 GB; 3.4-6.4 GB measured,
  HR1), never a fixed 8 GB; a host counts only its largest idle reservation. Every engine JVM (a head's, the served
  planner, a solver, offline A/B's) runs at a 512 MB thread stack (`campaign_engine_stack`): lowering recurses once
  per subterm, and a recorded term ~750 binary operations deep overflowed the default stack in an arm's key
  (solr-adhoc-19 SC7, the planner's round 3); a stack is reserved, only the depth a walk reaches is resident.
  A lowered text past 2048 characters is a `define-fun` its uses name (`SmtLowering#compact`): a nested substring
  chain held by value outgrew a 24 GB solver heap (solr-adhoc-10 SL2). A store leaf read through its node's view is
  lowered once per memo (`SmtLowering#throughView`, its answers kept as a node's are): a view's cases are leaves read
  through views of their own, and lowered anew at every use one arm's key spent 15 min there (solr-adhoc-40 SL1);
  a leaf of the view being cased is that case's own (one view read at ten versions was cased through every order).
- **Sweeps** (`tools/adhoc/sweep.sh <snapshot> <round> <cases-file> <heads-per-host>`): one `fanout.sh` job per case,
  at most `heads-per-host` heads on each lift (2 for the HDFS group), each admitted for the room it reserves, every
  case's obligations on all ten lifts; `CASE_TIMEOUT_SECONDS` (5400 s by default; 10800 for a full sweep) per case is a convenience of a shared
  cluster, not a verdict (a case cut there is rerun with a longer budget).
- **One case alone** (`tools/rounds/launch-run.sh <snapshot> <case> <suffix>`, or `launch-round.sh` with one case): a
  deep closure gets up to ~120 replays in flight (07 reached 121 with measured charges, against 15 under static
  charges). The final acceptance does not need it (owner 2026-10-05): cases run concurrently through the ledger with
  `CASE_TIMEOUT_SECONDS=10800`.
- **Agents' runs** go through the same ledger from their own snapshots and `GC_OUT`, so a lead's sweep and four
  agents' validation runs coexist; judge a crowded run by stage times and queue waits, not wall time.

## 3. Why cases were slow: the pitfalls, with numbers

| symptom | cause | fix |
| --- | --- | --- |
| QJM 07/08/09 ~82 min and cut by the budget; a replay waited a median 35 min for a slot (HG4) | every obligation charged a static 2500 MB (`obligation_memory_mb`), real peaks 170-700 MB; the sweep's per-case share computed from it (8 per lift) | measured charges, shared pool (MCH2: 07 reached its fixed point with up to 121 in flight) |
| 19's EXPLORE 776 s, 12 min of it waiting, though all 8 obligations were refused at their query (HG5A) | a solve that never replays waited for a replay charge | SOLVE / REPLAY split |
| seed and CONFIRM replays charged 8-11 GB for 0.5-2 GB peaks | recording x7 for every replay | x7 only before anything is measured; CONFIRM on the measured need |
| lifts 11-22 GB charged against 3-7 GB real use | the static charges above plus an idle 8 GB head reserve per lift | measured head need; remaining gap (~1.6x) is step charges at their start heap (kept: a refused growth would end a planner) |
| SEED 192 -> 542 s, INSTRUMENT 49 -> 129 s in a sweep's first wave | Soot class lookups on NFS (197K failed stats per pass), 20 heads starting together | `IndexedSourceLocator` (a lookup's folder listed once per JVM, a listed name Soot's own lookup) and the pass's JVM on the jar alone: ~7K failed stats per pass; outputs byte-identical over 12 HDFS cases; on a loaded cluster with warm NFS caches the walls did not move |
| a seed replay with 80-170 give-ups (start-up family) | DataNode actor turns decide by `monotonicNow` and the replay runs slower than the recording | the time family's workarounds on r7 (no external forks, synced edits, a settle before the window) and the wait deadline; the time model was reverted; a case at 80+ give-ups in a sweep is stopped, not waited out |
| 17 and 24 "UNSAT" with 151 / 3 obligations owed (HG5A) | the budget's reserve owes twice the longest COMPOSE + max(CONFIRM, seed REPLAY); a 22-min seed replay reserved 44 min and left EXPLORE none | EXPLORATION_CUT: such an end leaves no UNSAT; the real fix is the seed replay's speed |
| 16: PLAN_CLOSURE_CUT, 1542 occurrences over `schedule_max_jobs` | 1520 polling turns of `MarkedDeleteBlockScrubber` each planned as a task once control flow counted | E1: equivalent deciders planned once per class (1406 turns -> 55 classes) |
| 07: rounds proposing 180, 136, 587 obligations | the same (task, site, flip) arm re-asked under ~7.8 dependence digests on average; 47 of 189 re-asked arms changed verdict, so most is real work | open: dependence-key granularity (TODO); give the case the cluster |
| 07: COMPOSE silent for 17+ min over 556 sessions (HR1), past the case limit | `Composition#withoutFatalArm` looked for a refuted claim in each command with an `indexOf` reading to the end of the 26 MB body: commands x body size for every path of the self-check; and the reserve, before any COMPOSE was measured, owed it no more than the `campaign_reserve_s` floor (600 s) | each command's refuted-claim flag found once, from its last 64 characters; obligation workers' rows read 8 at a time; progress lines in `compose.log` (one per 25 paths, one per z3 run): 116-191 s offline (the corpus read 73-130 s from NFS), outputs byte-identical. Before a COMPOSE is measured, the reserve owes COMPOSE and EMIT the last planner round's wall each (07: 241 s; `campaign_last_round_millis`), never less than the floor |
| 07: `slots.jsonl` 1-1.9 GB (314,758 slots), read and rewritten by every round's planner (07e: 38-51 s and 194-208 s of a ~900 s round) | the slot table grows with every session's pairings | each round writes only its changes, `obligations-NNNN/slots.jsonl`, folded by its one reader; the served planner keeps the table |
| a replay's answer row corrupted when written from another host (MCH1) | rewriting a file in place over NFS: a client's cached copy wrote past a truncate | answers are written as a new inode and renamed |
| a branch window re-imported its whole closure per node (SB19 seed window 787 s) | O(n^2) re-import | stream the import, skip expanded nodes (183 s) |
| SGF3-adhoc-31's seed replay decode-bound (2026-10-13): 1666.5 MB read out, 2223 s decoding on the one publication thread (2426 s CPU in 2720 s), workloads waiting for room to hand on pages, the replay drifting off the recording (985 of 1636 slots given up) | every close reads out every location touched since its entry, so the enclosing activations re-read the inner ones' (394,232 versions listed for 51,043 write rows; every SGF3 case 2-7x), and the Zero interpreter decodes at 0.64-0.75 MB/s (a 17.5 MB page: table and closure 7.3 s, records parsed and expanded 14.6 s, version checks 3.9 s, reduction 1.7 s) | a record the store decoded with the exact same text is filed as that decoding, found by its location and one `regionMatches` (the same records in 0.87 s), an all-held page reads no table, a record is walked by one publication (VM.md §8, PIPELINE "A read-out repeats"): the 17.5 MB page again 0.77 s, with one record changed 3.3 s. Live (`gc-out/solr-readout`): SGF3-31's seed (RO2) read out 2640 MB in 1097 s decoding, 84 % of 344,822 envelopes held, took 1506 of 1627 slots (752 of 1636 before) and reached its target, seed replay ~44 min (~59); reindex-cleanup's (RO3) 35.0 s for 30.4 MB (48.9 s for 32.2 MB). A check build on SGF3-31's whole seed (RO1) decoded every held envelope again: 269,286, 0 differing; 103 all-held pages, no table row of theirs a node not yet expanded; the skipped walks would have claimed nothing. Still: the publication thread busy ~92 % (RO2: 2180 s in 2368 s), about half decoding the changed envelopes and the tables of pages holding one, half publishing first-time rows |
| Solr replays growing for minutes overcommitted lifts (SB11/SB13) | charges counted only during a 60 s ramp | life-long leased charges |
| six cases cut at 90 min in a 35-case sweep (HG9, 2026-10-06), e.g. 05 at 61 min with 60 verdicts and 105 replays in flight (alone in HG8W: 226 verdicts in 39 min) | 20 heads share the replay slots; the sweep's default `CASE_TIMEOUT_SECONDS=5400` is a share of the cluster | rerun at 10800 (11 26 33 37 closed); give a full sweep 10800 from the start |
| 11741 took 4.7-5.4 h though its witness landed after ~150 verdicts (AR1) | each solved obligation's REPLAY was put at the queue's front, ahead of the witness's CONFIRM: it waited behind 473 replays | a REPLAY goes behind a leading CONFIRM or RERUN (adffd6072) |
| 254 processes in NFS D state on lift11, load 288 (2026-10-06) | dozens of `offline-ab.sh` waiters each refreshed every host's ledger reading (ssh + mktemp + rename into one NFS directory) whenever the 5 s cache was stale | one refresher per host, the others use a reading up to 30 s old (b7c5dc99d); gates via `onlift.sh` off lift11 |
| a worktree took 45+ min to check out, a commit in it minutes | 99 % of the repository's files are `third_party/` (the VM's source) written to NFS | `tools/lib/worktree-add.sh`: sparse, 10 s |
| 11741's witness attempt stuck for hours (CC7, 2026-10-06) | `Cone.read` searched every assertion of another selector to the end of a 150 MB body for every path | the Cone read once and indexed by selector (3e7becca7) |
| a confirmed witness's verdict waiting behind a witness attempt | a returned confirmation is decided only by the next step, and steps run one at a time | minutes with the Cone fix (HF2: 15 min queue to accepted); `hdfs1-confirm-first` parked |
| solr-18413 Z3S: a witness attempted 69 min after its replay ended (2026-10-13) | a round and the gate shared one head step, one step at a time: the witness returned 3 s after a step began that planned round 2 (its planner out of 8 GB, then 1437 s waiting for 17.8 GB: 57 min), then GROW wove g3 in the head's hands for 8 min | rounds in a lane of their own over inputs frozen as each starts (`corpus.txt`, `answers.jsonl`, `in_flight.jsonl`), taken between two head steps: landing, the gate and witness attempts go on while a round plans (PIPELINE §7.9; shell row STREAM-WITFIRST) |
| solr-adhoc-07 RX6: the round-0 planner ran out of 8 then 16 GB over a 78 MB corpus (2026-10-12) | `SmtLowering`'s frames took a memoized node's unbound values again on every hit, as a list, so they doubled per level of a shared container chain; the arm keys lower every guard-location write | each frame holds a value once, by identity (`Raised#unbound`): round 0 in 8 s at 1.2 GB |

Older history is in `git log` of `run_engine.sh` and in PIPELINE §7.7's own examples.

## 4. How to debug a slow or stuck case

Never wait a slow case out: compare it with its peers and its history while it runs, find where the time goes, stop it
if it is clearly wrong, name the cause in code.

| question | tool |
| --- | --- |
| which cases of a round are where, with seed give-ups | `GC_OUT=... tools/rounds/round-status.sh <round>` |
| one line per finished case and per seed replay past 30/80 give-ups | `tools/rounds/round-watch.sh <round>` (under a Monitor) |
| which running case is past 2x / 4x its time in a baseline round | `tools/rounds/round-slow.sh <round> <baseline round>` |
| is a verdict real: how EXPLORE ended, z3 on the exported formula, BLOCKING gaps, moved roots, CONFIRM | `tools/rounds/round-verify.sh <round> [case...]` |
| where EXPLORE's time went: per verdict the run time and the queue wait, the concurrency over time, the refusal reasons | `tools/rounds/obl-times.py <case>/schedule` |
| time per stage, per round, per job | `out/<case>/schedule/stage_metrics.tsv`; `tools/analysis/timeline.py <case dir>` |
| what the exploration did per round | the log's `[campaign] round N (wave W): K obligation(s), E exposure(s), F in flight` and `exploration stopped (<END>)` lines |
| is the ledger the bottleneck | the log's `waiting for room: no host admits one more start (<host> has X MB charged ..., Y MB in use and Z MB held for a head ...)`; `ls -l $CAUSYNTH_HOST_LEDGER/<host>/charges/` (live = mtime < 120 s) |
| why a seed replay stalls | `grep -c 'did not happen' .../seed-result/focused/replay.log`, then which events did not happen and on which thread; `jstack` the replay JVM (`ps -g $(cat <run>/pgid)` on the head host) |
| where a JVM spends its time | sample `jstack <pid>` every few seconds (5-10 samples) and count the top frames; for IO, `strace -f -c` |
| a replay's memory | the replay log's `the workload JVM's resident memory peaked at X MB; its host was charged Y MB` |

Traps that cost hours: `stop-run.sh` matches every process whose command line names the run's directory, your own
shell included: run it alone on its command line (OPERATIONS.md §8). A `jstack` of a JVM whose working directory is a
case tree leaves `.attach_pid<pid>` there (FREEZE now tolerates a vanished file). A sweep with `PRUNE=1` deletes the
recordings the offline gate needs: keep `PRUNE=0` for a round you will gate against.

## 5. Open performance items (also in TODO.md)

0. **Incremental planning** (TODO HDFS §6, first; branch `solr-incr-plan`): in EX1-adhoc-07d the 16 planners took
   1h51m of EXPLORE's 2h25m (a round 2 s early, 19-22 min at ~640 sessions), so more lifts would buy 10-20 % at
   most. A late 07e round offline (~900 s): the corpus's rows 140-172 s, its indexes 24-39 s, the closure 190 s,
   the slot table read 38-51 s and rewritten 194-208 s, the frontier 168-177 s and the candidates 88-95 s (one
   `dependence` computed twice per arm, 227,681 asks). One planner now serves the exploration (PIPELINE §7.1),
   keeping the rows with what each session's rows alone give, the static map and the slot table, whose rounds
   write only their changes; within a round, `dependence` and the closure's re-walked pieces are computed once.
   07e's landing order replayed (`offline-ab.sh` EXPLORE.serve, no answers): 20 rounds, 2960 s with a planner of
   its own per round against 1667 s served, the late rounds 300-360 s against 150-180 s, every round's files
   identical (11741 60 -> 47 s, 09 162 -> 78, 39 76 -> 41, 17899-bug2 11 -> 7, solr-18406 94 -> 40, solr-18413
   125 -> 71). Live hdfs-adhoc-09 (INC1, beside other runs: 280 waits for ledger room): 76 rounds and 443 s of
   planning, at most 11 s a round, against EX1's 16 rounds, 234 s, at most 46 s; EXPLORE 1892 s against 845 s,
   with 675 verdicts (634 flips) against 566 (535): rounds come more often, each over fewer new sessions, and
   the corpus's landing order decides what each proposes (STATUS R4). Live solr-18413 (INC2, SAT confirmed):
   17 rounds, 298 s of planning, 150 s of it round 0 waiting for its 8 GB start, the rest 2-3 s a round, against
   SC1's 8 rounds and 348 s (one 185 s); EXPLORE 1113 s against 775 s beside other runs (94 waits for room).
   What a served late 07e round still spends:
   `Value#hashCode` recomputing deep part hashes (half its samples) and the closure.
1. COMPOSE on a large corpus (07: 556 sessions, 2-3 min offline): the corpus read is most of it, the slot table
   (07: 314,758 slots, now its rounds' changes folded) most of the rest; `Corpus#index` re-reads each session's
   schedule on one thread.
2. The seed replay's give-ups in the start-up/clock family: handled by workarounds (RULES); no time model.
3. EXPLORE: dependence-key granularity (re-asked arms, 07's snowball), measured before any change.
4. Step charges at the start heap (~1.6x real); a per-step measured charge needs a planner that survives a refused
   growth.
5. A host solver killed at its memory hold is placed by its measured peak or fails by name (`hdfs-solver-fallback`,
   in the body); 07's CC7 still lost 8 obligations to a full host (no host had room within the 60 s placement wait).
6. 17897's COMPOSE: two z3 runs per satisfiable ask, whole asks 16-56 s (measured on `hdfs-compose-perf-wip`,
   bundled in `/bigtemp/vnr3ne/handover/2026-10-08/graphchecker-remote-branches.bundle`).
7. The two-phase final run (TODO HDFS §1): short cases a few at a time, deep closures each with the whole cluster.
8. **A hard question held its host's solver** (SP4-10/13, 2026-10-12; branch `solr-solve`): a host's solver answers
   one question at a time, and obligation solves ran at the full 1810 s z3 budget. Answered questions took a median
   1 s (p90 3-4 s, max 9 s), but 16 READ-door (`SolrZkClient.getData`) and routed-alias
   (`MaintainRoutedAliasCmd.call`, `TimeRoutedAlias.<init>`) flips ran their z3 races 1000-1180 s, holding 10's
   whole solve share: 292 questions queued (median wait 1135 s), throughput from ~250 to ~140 verdicts/h. Now two
   lanes (PIPELINE §7.5): every question first at 60 s; one undecided goes to a hard lane at the full budget in a
   JVM of its own once nothing else waits; a question its host's solver leaves untaken 30 s goes to a JVM of its own.
   Gate: the shell rows SOLVE-LANES*, a live solr-adhoc-10. Then the memory those solvers held (SL1-10): host solvers
   at the 16 GB engine heap grew to 6-12.5 GB resident over a live set of 0.85 GB after a full collection, one per
   host and campaign, and filled every lift's ledger; a question's own JVM charged 512 MB was ended at its first
   growth on a full host and its retry asked the largest host solver's 12.5 GB (OBLIGATION_UNFINISHED after 600 s).
   Now a corpus's solvers start at 2 GB and double on an out-of-heap exit, charged their footprint, and a retry is
   placed by its own JVM's need (PIPELINE §7.5; shell rows SOLVER-HEAP and the retry rows).
9. **GROW in the head's hands** (TODO): a round that exposes regions is taken with GROW's planner and weave run
   synchronously by the head (`campaign_stream_take_round` -> `campaign_stream_grow`), so no start is dispatched,
   nothing lands and no witness is attempted until the weave returns (solr-18413 Z3S round 2: 8 min). Rounds and
   witness attempts already run beside the head (PIPELINE §7.9); GROW would be a step of a lane too.
10. **Known limits of the two lanes** (PIPELINE §7.9). Both may wait for memory at once: a round's planner and a
   witness's composer are each placed by its own charge, each holding its need on the roomiest host while it waits
   (two holds, maybe on one host), and the head's room covers one of them -- an attempt no longer waits behind a
   round, but it can still wait for room (Z3S's planner waited 1437 s for 17.8 GB). A round's directory is written by
   the planner, maybe on a peer, and renamed `planning-NNNN` -> `obligations-NNNN` by the head on its own host: a
   reader elsewhere finds the new name by a lookup at the server, but an NFS client that looked that name up before
   the rename (no reader names a round before it is taken) would hold a negative entry for its attribute-cache time.

## 6. Every HDFS case alone on the ten lifts (series EX1, 2026-10-07/08)

The owner's measurement (2026-10-07: "把46个case的每一个，独占集群跑完，每个case并行可以充分使用10个server。统计time breakdown ...
以及每个case闭包最终的region总数"): each of the 46 cases ran alone, one after the other, its obligations, replays and
head steps over all ten lifts (no shared pool), on the branch that closed it (`system/hdfs` locked body, snapshot
`~/gc-run/hl1`; `system/hdfs1` 8c446418b, snapshot `~/gc-run/rp5`, for 07 11741 21 29 30 39 40). Driver
`/bigtemp/vnr3ne/analysis/excl-2026-10-07/excl-driver.sh` (queue, PAUSE/STOP files), outputs
`/bigtemp/vnr3ne/gc-out/hdfs-excl/accept-EX1-<case>/`, numbers by `stats.py` beside the driver, from each run's
`stage_metrics.tsv`:

- **analysis** = PREFLIGHT, FREEZE, SETUP, SEED (static passes, recording, trace aggregation), PLAN, INSTRUMENT, the
  seed REPLAY and IMPORT; **exploration** = EXPLORE (planner rounds, solves, replays, GROW); **compose+solver** =
  COMPOSE + SOLVE + DECIDE; **other** = CONFIRM, EMIT, REPRODUCE (the acceptance harness's z3 probe and report after
  the campaign are not counted).
- **regions** = the distinct regions of the final closure (the last generation's `execution_task_plan.jsonl`);
  **occurrences** = its rows (planned occurrences); **rounds** and **verdicts** = EXPLORE's planner rounds and
  obligation verdicts.

Totals: 54886 s (15.2 h) of campaign wall time; analysis 26326 s (48 %), exploration 25369 s (46 %), compose+solver
2009 s (4 %). Median case 762 s; analysis is the median case's larger part (64 %), serial and unaffected by more
lifts. One case past an hour (07, 11113 s: 16-20 serial planner rounds over ~640 sessions, TODO HDFS §6 incremental
planning), five between 30 and 45 min (11741 2626, 26 1892, 24 1857, 08 2060, 09 1929). Regions per closure: median
11, from 1 (31, 48) to 28 (11). Against the shared HL1 round (43 cases, 1 head per lift) the deep closures ran 2.5-5x
faster (08 5982 -> 2060 s, 09 6519 -> 1929, 14 3814 -> 1182, 17897 2126 -> 443) and the short ones the same.

| case | branch | verdict | wall (s) | analysis (s) | exploration (s) | compose+solver (s) | other (s) | regions | occurrences | rounds | verdicts |
| --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| hdfs-17897 | hdfs | SAT | 443 | 236 | 169 | 15 | 20 | 12 | 13 | 4 | 30 |
| hdfs-17899-bug1 | hdfs | SAT | 430 | 284 | 121 | 2 | 19 | 14 | 20 | 2 | 23 |
| hdfs-17899-bug2 | hdfs | SAT | 594 | 342 | 201 | 17 | 24 | 11 | 14 | 6 | 54 |
| hdfs-17899-bug3 | hdfs | SAT | 418 | 248 | 147 | 2 | 18 | 9 | 16 | 2 | 22 |
| hdfs-17967-pathA | hdfs | SAT | 398 | 232 | 144 | 2 | 17 | 12 | 13 | 2 | 8 |
| hdfs-17967-pathB | hdfs | SAT | 367 | 232 | 114 | 2 | 17 | 11 | 12 | 2 | 8 |
| hdfs-17967-pathC | hdfs | SAT | 433 | 246 | 161 | 4 | 18 | 11 | 12 | 3 | 18 |
| hdfs-17960 | hdfs | SAT | 614 | 341 | 249 | 2 | 20 | 5 | 6 | 4 | 79 |
| hdfs-11741 | hdfs1 | SAT | 2626 | 525 | 1664 | 228 | 202 | 15 | 31 | 6 | 1419 |
| hdfs-bugs-slowdisk-zero | hdfs | SAT | 412 | 215 | 172 | 2 | 20 | 5 | 6 | 4 | 40 |
| hdfs-adhoc-05 | hdfs | UNSAT | 633 | 441 | 167 | 9 | 14 | 7 | 17 | 7 | 193 |
| hdfs-adhoc-06 | hdfs | UNSAT | 635 | 444 | 165 | 9 | 14 | 7 | 17 | 7 | 193 |
| hdfs-adhoc-07 | hdfs1 | UNSAT | 11113 | 672 | 9601 | 519 | 302 | 12 | 31 | 20 | 2284 |
| hdfs-adhoc-08 | hdfs | UNSAT | 2060 | 564 | 862 | 601 | 29 | 7 | 9 | 17 | 484 |
| hdfs-adhoc-09 | hdfs | UNSAT | 1929 | 564 | 845 | 484 | 33 | 7 | 9 | 16 | 566 |
| hdfs-adhoc-10 | hdfs | SAT | 783 | 600 | 161 | 2 | 17 | 11 | 17 | 2 | 46 |
| hdfs-adhoc-11 | hdfs | UNSAT | 1135 | 451 | 665 | 7 | 7 | 28 | 86 | 9 | 42 |
| hdfs-adhoc-12 | hdfs | SAT | 693 | 404 | 261 | 4 | 21 | 10 | 11 | 2 | 22 |
| hdfs-adhoc-14 | hdfs | UNSAT | 1182 | 431 | 724 | 11 | 14 | 17 | 26 | 12 | 95 |
| hdfs-adhoc-15 | hdfs | UNSAT | 901 | 432 | 455 | 2 | 3 | 12 | 84 | 2 | 13 |
| hdfs-adhoc-16 | hdfs | UNSAT | 1352 | 877 | 460 | 2 | 3 | 13 | 119 | 2 | 26 |
| hdfs-adhoc-19 | hdfs | UNSAT | 634 | 540 | 87 | 2 | 3 | 5 | 6 | 2 | 36 |
| hdfs-adhoc-20 | hdfs | UNSAT | 505 | 476 | 7 | 4 | 3 | 13 | 61 | 2 | 12 |
| hdfs-adhoc-21 | hdfs1 | UNSAT* | 1417 | 803 | 596 | 3 | 4 | 8 | 10 | 4 | 15 |
| hdfs-adhoc-22 | hdfs | UNSAT | 1510 | 1006 | 489 | 4 | 6 | 15 | 66 | 4 | 45 |
| hdfs-adhoc-23 | hdfs | UNSAT | 1774 | 1020 | 739 | 4 | 6 | 15 | 65 | 5 | 45 |
| hdfs-adhoc-24 | hdfs | UNSAT | 1857 | 1286 | 556 | 5 | 6 | 15 | 65 | 4 | 35 |
| hdfs-adhoc-25 | hdfs | UNSAT | 1429 | 967 | 444 | 5 | 9 | 15 | 66 | 9 | 81 |
| hdfs-adhoc-26 | hdfs | UNSAT | 1892 | 1491 | 385 | 4 | 5 | 15 | 67 | 4 | 40 |
| hdfs-adhoc-27 | hdfs | UNSAT | 892 | 684 | 189 | 4 | 9 | 15 | 77 | 4 | 28 |
| hdfs-adhoc-28 | hdfs | UNSAT | 533 | 521 | 6 | 2 | 2 | 2 | 2 | 2 | 2 |
| hdfs-adhoc-29 | hdfs1 | UNSAT | 395 | 382 | 6 | 2 | 2 | 2 | 2 | 2 | 1 |
| hdfs-adhoc-30 | hdfs1 | UNSAT | 428 | 408 | 13 | 2 | 3 | 3 | 7 | 2 | 6 |
| hdfs-adhoc-31 | hdfs | UNSAT | 329 | 317 | 6 | 2 | 2 | 1 | 1 | 2 | 1 |
| hdfs-adhoc-33 | hdfs | UNSAT | 742 | 501 | 220 | 7 | 12 | 2 | 2 | 7 | 45 |
| hdfs-adhoc-34 | hdfs | UNSAT | 1436 | 943 | 478 | 4 | 6 | 15 | 64 | 5 | 45 |
| hdfs-adhoc-35 | hdfs | UNSAT | 1706 | 984 | 708 | 4 | 5 | 16 | 65 | 4 | 35 |
| hdfs-adhoc-37 | hdfs | UNSAT | 1763 | 1487 | 261 | 4 | 5 | 15 | 68 | 4 | 36 |
| hdfs-adhoc-38 | hdfs | UNSAT | 466 | 450 | 6 | 2 | 2 | 12 | 61 | 2 | 1 |
| hdfs-adhoc-39 | hdfs1 | UNSAT | 1197 | 512 | 661 | 7 | 12 | 9 | 64 | 15 | 92 |
| hdfs-adhoc-40 | hdfs1 | UNSAT | 548 | 330 | 211 | 2 | 3 | 7 | 9 | 4 | 9 |
| hdfs-adhoc-45 | hdfs | UNSAT | 418 | 405 | 7 | 2 | 2 | 3 | 3 | 2 | 10 |
| hdfs-adhoc-48 | hdfs | UNSAT | 470 | 458 | 6 | 2 | 2 | 1 | 1 | 2 | 1 |
| hdfs-adhoc-49 | hdfs | UNSAT | 1677 | 523 | 1138 | 2 | 10 | 9 | 26 | 5 | 241 |
| hdfs-adhoc-50 | hdfs | UNSAT | 895 | 348 | 533 | 2 | 8 | 9 | 30 | 4 | 141 |
| hdfs-adhoc-52 | hdfs | UNSAT | 822 | 703 | 109 | 2 | 2 | 3 | 55 | 3 | 4 |

Notes: verdicts are the runs' claims, checked with `round-verify.sh` (`ex1-verify.txt` beside the driver): every
`system/hdfs` case repeats its HL1 verdict and `.smt` shape (the same four NO-SYMBOL UNSATs, 28 31 45 48, with their
STATUS reasons). UNSAT* = 21's accepted RUN_DEFECT residue (1 BLOCKING `ADMISSION_GAP` of the stranded actor body,
TODO HDFS §4; W21 had 3). 07 is its fifth attempt, EX1-adhoc-07e (07 on rp1 12588 s RUN_DEFECT, 07b/07c stopped,
07d 10238 s UNSAT with 11 unfinished obligations); 29 is its rerun EX1-adhoc-29b (the first seed replay missed the
anchor on a racy start-up, CHECKING trap 15). 11741 is BOUNDED after its witness (one task deferred past 32 paths),
which a confirmed SAT does not rest on; its cone is unbound 0. The lead's builds and offline gates ran beside 08, 15,
17899-bug1, 09, 07d and 07e for a few minutes each, and another user's IDE held ~4 GB on lift12 throughout.
