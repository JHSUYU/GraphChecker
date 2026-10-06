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
  seven times the recording's measured peak (capped at half a host). Obligation replays peak within +-10 % of their own
  seed replay (HG4: 11741 674 / 662-715 MB; adhoc-07 238 / 194-257; outlier adhoc-15 514 / up to 2003, which grows
  through the ledger).
- **An obligation is two starts**: its SOLVE (charged what a solver starts at, 1 GB; answered by its host's warm solver
  when one serves) and, only when the solver answers SAT_MODEL_READY, its REPLAY, queued first at once, on the class
  tree and plan its solve started on. Until the replay lands the obligation is in flight (never re-proposed). Most
  obligations end at the solve (UNSAT, refused), so they never wait for replay memory.
- **The shared pool** (a sweep, `stream_shared_pool=true`): the explorations running at once divide the pool's slots
  (as many replays as fit under the ceiling at the measured charge, at most the cores, per host) by the number of
  explorations whose entry in `$CAUSYNTH_HOST_LEDGER/explorations/` is fresh, re-read at every start. One case alone
  keeps all of it; ten keep a tenth each, and a share grows as others end. A named acceptance run shares nothing.
- **Head steps** (PIPELINE §7.7 HEAD STEPS): every engine JVM of a head (static passes, planner, composer, CONFIRM's
  main, GROW's planner) goes to the head's own host if it fits, else to the pool's host with the most room, charged
  at the heap it starts at; a step that waits holds its need on the best host so that host drains. A head holds room
  for its next step: its measured step need (the largest engine JVM peak x1.25, at least 1 GB; 3.4-6.4 GB measured,
  HR1), never a fixed 8 GB; a host counts only its largest idle reservation.
- **Sweeps** (`tools/adhoc/sweep.sh <snapshot> <round> <cases-file> <heads-per-host>`): one `fanout.sh` job per case,
  at most `heads-per-host` heads on each lift (2 for the HDFS group), each admitted for the room it reserves, every
  case's obligations on all ten lifts; `CASE_TIMEOUT_SECONDS` (5400 s) per case is a convenience of a shared cluster,
  not a verdict (a case cut there is rerun alone).
- **Exclusive runs** (`tools/rounds/launch-run.sh <snapshot> <case> <suffix>`, or `launch-round.sh` with one case):
  the final acceptance runs each case alone on the whole cluster; a deep closure gets up to ~120 replays in flight
  (07 reached 121 with measured charges, against 15 under static charges).
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
| a seed replay with 80-170 give-ups (start-up family) | DataNode actor turns decide by `monotonicNow` and the replay runs slower than the recording | the time model (`Clocks`, PIPELINE §5): 25 34 35 at 0-2 (no model 6-91), 23 83 -> 37, 22 66 -> 43, 01 84 -> 30-61; 17 21 43 52 still vary run to run on causes that are not the clock (TODO §3); a case at 80+ give-ups in a sweep is stopped, not waited out |
| 17 and 24 "UNSAT" with 151 / 3 obligations owed (HG5A) | the budget's reserve owes twice the longest COMPOSE + max(CONFIRM, seed REPLAY); a 22-min seed replay reserved 44 min and left EXPLORE none | EXPLORATION_CUT: such an end leaves no UNSAT; the real fix is the seed replay's speed |
| 16: PLAN_CLOSURE_CUT, 1542 occurrences over `schedule_max_jobs` | 1520 polling turns of `MarkedDeleteBlockScrubber` each planned as a task once control flow counted | E1: equivalent deciders planned once per class (1406 turns -> 55 classes) |
| 07: rounds proposing 180, 136, 587 obligations | the same (task, site, flip) arm re-asked under ~7.8 dependence digests on average; 47 of 189 re-asked arms changed verdict, so most is real work | open: dependence-key granularity (TODO); give the case the cluster |
| 07: COMPOSE silent for 17+ min over 556 sessions (HR1), past the case limit | `Composition#withoutFatalArm` looked for a refuted claim in each command with an `indexOf` reading to the end of the 26 MB body: commands x body size for every path of the self-check; and the reserve, before any COMPOSE was measured, owed it no more than the `campaign_reserve_s` floor (600 s) | each command's refuted-claim flag found once, from its last 64 characters; obligation workers' rows read 8 at a time; progress lines in `compose.log` (one per 25 paths, one per z3 run): 116-191 s offline (the corpus read 73-130 s from NFS), outputs byte-identical. Before a COMPOSE is measured, the reserve owes COMPOSE and EMIT the last planner round's wall each (07: 241 s; `campaign_last_round_millis`), never less than the floor |
| 07: `slots.jsonl` 1 GB (314,758 slots), rewritten by EXPLORE every round and most of COMPOSE's remaining read | the slot table grows with every session's pairings | open (TODO) |
| a replay's answer row corrupted when written from another host (MCH1) | rewriting a file in place over NFS: a client's cached copy wrote past a truncate | answers are written as a new inode and renamed |
| a branch window re-imported its whole closure per node (SB19 seed window 787 s) | O(n^2) re-import | stream the import, skip expanded nodes (183 s) |
| Solr replays growing for minutes overcommitted lifts (SB11/SB13) | charges counted only during a 60 s ramp | life-long leased charges |

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

1. COMPOSE on a large corpus (07: 556 sessions, 2-3 min offline): the corpus read is most of it; the 1 GB
   `slots.jsonl` (07: 314,758 slots) is rewritten by EXPLORE every round and is most of COMPOSE's remaining read;
   `Corpus#index` re-reads each session's schedule on one thread.
2. The seed replay's give-ups: the time model (the start-up/clock family) -- also the biggest correctness item.
3. EXPLORE: dependence-key granularity (re-asked arms, 07's snowball), measured before any change.
4. Step charges at the start heap (~1.6x real); a per-step measured charge needs a planner that survives a refused
   growth.
