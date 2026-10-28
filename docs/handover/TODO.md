# TODO: Solr finished -- what is left on this branch (2026-10-26)

Solr is finished (2026-10-26, section "Solr: after the owed cases"): all 20 cases have their `.smt` (`results/solr/`);
what is left is optional engine work, each item with its evidence. The other systems' plans are on their own branches
(README "Branches"): HDFS on `system/hdfs-liftlab`, HBase on `system/hbase`, ZooKeeper on `system/zookeeper`; the old
Solr bugs put back by hand on `system/solr-buggy-detect`.

The owner: "hdfs所有的case跑完为一组，不要有回归。然后就到另一个系统". Each system is finished when every one of its
checks has an exported `.smt` that is right (SAT confirmed, or UNSAT at the fixed point) and every known bug of it
passes. Branch, tree and path details are in [STATE.md](STATE.md); every check with its state in
[../checks/README.md](../checks/README.md) and its reading in [../STATUS.md](../STATUS.md); commands in
[OPERATIONS.md](OPERATIONS.md); speed and the cluster in [../design/PERFORMANCE.md](../design/PERFORMANCE.md).

## HDFS engine follow-ups (general items, open on this body; the HDFS record is `system/hdfs-liftlab`)

This branch carries `system/hdfs1`'s HDFS cases and engine (STATE §0): 46 of 46 cases closed there with a hand-read
`.smt` (STATUS "HDFS checks"), no new bug. What is left from them is the general work the workarounds stand in for, the
defects that session found, and the cleanup; an engine change below reruns the affected cases (one change per round,
RULES "Lock, then one change at a time"). The HDFS checks themselves now run on `system/hdfs-liftlab` (its TODO).

### 1. The two-phase final acceptance run (owner 2026-10-06): done another way
Series H1 on `system/hdfs-liftlab` (2026-10-27) ran every HDFS case but 11741 alone on liftlab (`results/hdfs/`).

### 2. The general fixes the workarounds stand in for
- **21**: a loop root's prefix as its own occurrence (§3) and the stranded activation (§4); then 21 runs on r7 without
  its tree and loop-bounds file.
- **07**: index a decoded reply's consumer by the send ordinal of the request it answers, not by the order the code reads
  it (STATUS open defect 57; `MessageDoors#send` records correlation id -> ordinal, `Identity#endpointAt`,
  `WireExport#attachLeaf`; ~50 lines + a test). Needed for HBase and ZooKeeper too (they iterate replies out of
  `HashMap`s). Then 07 runs on r7 without r8, and its world depth back at the default if it converges.
- **The time family** (21 22 23 24 25 34 35 52): the r7 workarounds (STATUS "Per-system surface") stay; the time model
  is never ground on (RULES).

### 3. A loop root's prefix as its own occurrence (general fix for 21's tree workaround; design ready)
A LOOP_BODY_ROOT occurrence's activations are its loop's iterations, so what its root method runs before the loop
is observed by none (21: `BPServiceActor.run`'s handshake, `checkNNVersion`). Merging the prefix into the first
iteration (branch `hdfs1-prefix-span` 1f14e68c7) stretched the actor occurrence over the whole service loop: its
offerService iteration never reaches a terminal, so an admitted replay's rows go unpublished (PS2-21: a BLOCKING
nested cut on an unstated flip), and every arm is keyed by the heartbeats delivered after it (PS1-11: 1319 asks).
Design: (1) the prefix's address is the loop-body occurrence's plus one index frame `<loopRuntimeId>:prefix@0`
(`OccurrenceAddress#prefix`, one function for PLAN and the runtime); (2) PLAN gives a LOOP_BODY_ROOT region whose
root method calls region work before the loop header a PREFIX task (same region, node and loop-root hook group,
rootAuthority `LOOP_PREFIX`), and the declared anchor goes on it when the root-method call it is reached through
lies outside the loop body; (3) `LoopAccounting#enterLoopRoot` opens the prefix task's activation, the first body
entry ends it NORMAL (published) and admits the body's own as on the merged body, the root's exit ends it with no
iteration, a cut ends it CUT; it counts against no loop-body budget; `PrefixSpan#atBody` and the "one activation,
two spans" text go; (4) no key change. Offline (PS1-11, current key): the actor's (arm, key) pairs 17008 merged,
7216 split (prefix 5327, body 1889); the prefix joins 11's closure as an `allKeys` writer, which the merged body
never did. Still owed with it: an activation stranded at session end publishes CUT (no ADMITTED verdict over
unpublished rows).

### 4. A stranded activation's rows (21's residue; evidence: W21's 3 BLOCKING gaps)
An activation whose root is still running when the session ends is stranded (`ConcolicResultPublisher#
strandWithoutTerminal`, TERMINAL_NEVER_REACHED): its path is withheld, only its mints publish, yet the replay's
verdict can stand ADMITTED (`FocusedReplay` saw the flipped arm taken). A nested path then cut from that session
inherits a flip the session does not state: W21 (`/bigtemp/vnr3ne/gc-out/hdfs-21w/accept-W21`), BLOCKING EXPLORE
`ADMISSION_GAP`s `updateActorStatesFromHeartbeat` u93#2/#3/#5 at the actor body occurrence 1bc6719160f7e094
(obligations ce70720a45fc2503, 12f86ac9a0cf4a8a, 97207921c23d9e9c); 4 of W21's 5 sessions stranded that body
(PS2-21: the same at u93#4). Fix, one of: (a) a stranded activation publishes CUT, as a bounded cut does: the VM
region closes only on its own thread, so the strand asks the owner thread to end at its next hook (a held
schedule wait released at session end) through `LoopAccounting#endAtCut`, the barrier waits for it under the same
grace, and one that reaches no hook makes its replay's obligations admit nothing
(`FocusedReplay#noteUnsettledPublication`), no new verdict; or (b) no nested path is cut from a session whose
flipped activation published no rows. Today's corpora of 07 (CC7), 11741 (AW5), 29 30 40 (HF1) and 39 (WD3) hold
no stranded activation, so either touches only perpetual bodies like 21's actor.


### 5. Defects found this session (STATUS "Open defects" has each with its fix)
- **52-56, codec capture review**: a getter on a message no door decoded attaches nothing, silently (52); SEED derives
  no port for a two-field getter or an unresolved class (53); a refused setter export leaves the builder's earlier
  element bound (54); the input-shape key does not record which producer fed which site (55); a protobuf object kept
  as state is not tracked as state (56). None is on a closed case's path (the review read 07, 11741, 12).
- **58/59, open-arm bookkeeping** (T): an obligation id carries no path and no world, so two worlds can share one; and
  the id drifts as the corpus grows. 39 closes, but its closure varied run to run before the open-arm keys (CHECKING
  trap 18).
- **51**: the arm key's u18#3 gap (rule 1 and the own-fault key missed the throughput bar; branches parked).
- **Confirm-first**: merged on `system/solr` (2026-10-08): solr-18406 SG3V's confirmation waited 46 min behind a witness
  attempt's COMPOSE that waited for head memory.
- **Scope (B)**, widening that would only make right formulas more flippable: 29/30 the block-pool map written at
  DataNode start-up and `bpServiceToActive`'s in-window writer gated by HA state; 17's lease and 39's IBR ordering
  (turns on threads with no schedule events); an identity compare of a tracked reference with an enum constant states
  no VM term (VM.md §5.2); 05's thread-local buffer invariant; String fields (21's versions; defect 34); 14's retry
  identity and its constant arm; 11's u18#3 key gap; 20's txid.
- A possible flake: Mockito `UnfinishedStubbingException` in `TestBlockRecovery2`.

### 6. Speed (PERFORMANCE.md §5)
- **Incremental planning** (owner 2026-10-07: "这个优化记做todo吧"; the first speed item): merged on
  `system/solr` (7e7bb64c2, 2026-10-08; not on the HDFS branches). One planner JVM serves an exploration's rounds (`ExploreMain --serve`,
  PIPELINE §7.1/§7.9), keeping the corpus's rows with what each session's rows alone give, the static map and the
  slot table, whose rounds write only their changes; within a round `dependence` and the closure's re-walked
  pieces are computed once. Gate `offline-ab.sh` `EXPLORE.serve` identical on EX1 07e, 11741, 09, 17899-bug2, 39
  and SC1 solr-18406/18413 (07e: 2960 s fresh against 1667 s served, late rounds 300-360 against 150-180 s;
  PERFORMANCE §5 item 0). Live (rounds INC1/INC2, their outputs since deleted): INC1-adhoc-09 UNSAT_CLOSED as EX1,
  76 rounds and 443 s of planning (EX1: 16 rounds, 234 s); INC2-solr-18413 SAT_CANDIDATE CLOCK_SKEW confirmed.
  Still open: (1) rounds now come more often, each over fewer new sessions, and 09 asked 675 obligations (634
  flips) against EX1's 566 (535): measure whether frequent rounds propose arms under keys that later drift, and
  whether a round should wait for more landings; (2) `Value#hashCode` recomputes deep part hashes, about half of
  a late served 07e round's samples: a cached hash needs an immutability audit of the 35 contract values; (3) the
  closure is still built whole each round.
- **The planner's heap still grows with the rounds** (STATUS open defect 37). With the closure walk's reads indexed once
  per member and the expression tables compact, 39's PV7 round 6 (208 sessions, 9.8 GB) plans in 806 s at 16 GB,
  peaking near 9.4 GB live; a lowering frame's side conditions are held by reference and `Independence`'s leaf sets as
  arrays (SGF7-adhoc-10's subset: 1626 -> 1008 MB after the round, adhoc-40's 1649 -> 1163). What is left grows with the
  corpus and the rounds, spread wide (STATUS 37 has the measured shares): (1) strings -- the corpus indexes' composed
  keys, the joins', the endpoints' and locations' (done 2026-10-18, OPTIMIZATIONS 1.26-1.30: 05 r5's planner 12.7 ->
  3.5 GB at its walk's end); left: the lowered and shared bodies' texts the memos keep for the round, and the
  expression nodes the memo's keys hold strongly; (2) the slot table, whose
  rounds' changes every planner folds (`SlotTable#read`: 966K slots after round 5; its endpoints and frames held once
  per read since 1.28) and whose round 6 change file was 2.9 GB, a full endpoint per row; (3) the walk's per-session repetition (each session's demanded reads ask the same
  static candidates again; `Walk#holders` dominates its CPU: about half of round 6's 13 minutes).
- 11741 takes 1.5 h on the cluster (HF2: witness at ~60 min, confirmed at ~75 min, 5168 s in all).
- The ledger's ~1.6x over real use (step charges at their start heap).

### 7. Cleanup still owed (RULES: every change deletes what it replaces)
- The four-hop door API: `MessageDoors` should call `RuntimeTraceContext` directly.
- `CausynthTraceRecorder`'s offline aggregation into its own class; `CausynthPipeline`'s weaves apart from the analysis
  orchestration.
- The COMPOSE refactor's step 5 (steps 1-4 are in): `Composer.compose`/`run` as named steps; `SmtLowering` ->
  `VmTermLowering` + `SmtSymbolTable`; gated identical (`offline-ab.sh`, COMPOSE).
- The VM's dead natives and `exportLeaf`/`mintLeaf` with the next VM build (STATE §3).
- Loop-bound rows keyed structurally, not by Jimple unit ordinals (a tree change renumbers `#uN`).
- Left by the 2026-10-08 cleanup, each needing a decision: `DependencyRole` (its constant is hashed into task
  digests: deleting it re-keys every arm); STATUS open defects 14-16 (ClosurePlanner's fallback, SelectorResolution's
  degraded address, ScheduleLog's malformed timeout: semantic changes, design first); the two option parsers
  (`LongOptions`, `parseArgs`: merging changes how a bad command line is refused).
- `offline-ab.sh` `ab_stage_seed_static` tests `-s GROWN` on the gate host right after another host wrote it; over NFS
  it can miss the file (one spurious SEED.static difference on 2026-10-08): wait for it, or read it on the writer.

## Solr: after the owed cases (2026-10-26) -- the current plan

Read [START-HERE.md](START-HERE.md) and STATE.md §S first. `system/solr` (pushed) holds the rewrite, SGF9's fixes and the
five the owed cases found (STATE §S); every case's final run, `.smt` and time row is `results/solr/`. Evidence of the
owed cases: `/bigtemp/vnr3ne/analysis/solr-2026-10-22/lead/` (RUNS.txt, vacuity-<run>.txt). Merge each branch into an
integration branch from `system/solr`, gate it (mvn package with tests +
`src/test/shell/run_engine_campaign_helpers_test.sh` on an idle host), fast-forward `system/solr`
(`/bigtemp/vnr3ne/wt/gc-solr`). Branches named below that are not on GitHub were local and removed in the 2026-10-28
cleanup; each is named with its head commit.

**1. The owed cases: done** (2026-10-22..26): 05 07 09 13 14 19 31 39 each ran alone (X1/X1B/X1C) after the
concurrent rounds R1-R4 found five defects, now fixed (STATE §S); verdicts in `results/solr/`.

**1b. What the owed cases left open** (none blocks a verdict):
- Head steps starve under concurrency: eight Solr cases at once left R1-14's planner unstarted for 30 min (each head
  step wants ~23 GB beside the others' replays; `system/hbase`'s TODO item 15 is the same starvation). Run Solr at <= 3 at once, or give
  a waiting head step priority over new replay starts.
- The target not reached: 13 (123 paths) and 31 (134 paths, 35 TOPOLOGY_DIVERGENCE) compose no path through the target
  occurrence; 13's closure is truncated at the task bound, 31's replays diverge from the recording's cluster. Find which
  occurrence chain leads to the target and why GROW does not task it.
- 19's unplaced clock cells (item 5 below) still refuse most of its paths (7 composed).
- 14's COMPOSE: ~50 s a path at 21504 MB (117 paths, 1.5 h); the body per path (`Corpus#holding`) is the cost.
- 39's counterfactual (re-pairing the `AliasesManager.aliases` reference) is outside its guard's slice: the slice stops
  at the immutable map it reads.

**2. The decide's z3 on big bodies** (OPTIMIZATIONS 1.52, 1.53; `z3slot/`). A memout now doubles every pair's slot
while the host holds it (05's shared part needs 2662 MB a z3, reads in 89 s at 4096 MB against the 120 s remote read
limit); one heavy question halves every host's pairs. Left: 22 of 05's 340 paths hit the 60 s per-path limit; questions
that want an unsat core go only to the local pair (4316 MB room on 05, would answer memout); the body is still built as
one String.

**3. GROW rows carry their shape -- branch solr-growshape 727d48ea5 (gated, NOT merged).** Most GROW re-runs re-expose
an occurrence already planned under another name (tick ordinal, anchor id, loop index: timing counts): rename-only
re-runs 05 19, 40 25, 10 13 (its 34-min tail), 19 80, 09 8 (`growchain/FINDINGS.txt`). GROW rows lacked the
contextShape/recordedBeside seed rows carry, so the runtime's answer-by-shape could not take them. The branch fills
both through the one ContextShape path; offline (`growshape/`) 23-39 of 05's 54 renames are answered (one activation
per row: 903 non-demanded same-shape activations may take a row first), 1019a08704dc2746's last two re-runs (2734 s of
replay) go, 10 saves ~5 min; no genuinely new exposure is answered. Before merging: measure on one case's replays what
the extra instrumented activations cost in read-outs (item 4).

**4. Read-out volume after doors-only roots run whole.** 05's replays went decode-bound at generation g14 (a fresh
weave that ran the Overseer task roots whole): read-outs 81 MB -> 1.0-1.65 GB, versions 57 K -> 3.5-6.0 M, decoding ~0.9
of each window, windows 136 -> 1659 s, the REQUESTSTATUS polls 28 -> 1685 (`growchain/FINDINGS.txt` Q4). The single
largest replay cost seen in SGF9; confirm which roots produce the volume, then bound it.

**5. Smaller items, each with its evidence.**
- Unplaced clock cells: 19 composed 2 of 44 paths (41 refused, `Composer#unplacedClocks`); placing node0's clock cell
  composes 28 of 44 and still decides NO_SUPPORTED_WITNESS (`c19/FINDINGS.txt`).
- A re-run that lands mid-round is seen one round late (~6.5 min a link; 50 of 1019's 160 min were waits).
- Chains of doors-only growths: with the fixed point waiting for every re-run (b9ecc0ba2), the fresh-clone run of 38
  (`accept-FC6STOP-adhoc-38`, no witness that run) spent rounds 47-64 growing one doors-only occurrence "run whole" at a
  time, one re-run each (~5 min a link), still going when stopped: batch a round's doors-only occurrences, or bound
  what a whole-run occurrence adds (item 4).
- COMPOSE's read (~120 s on 40) and admission (~104 s) after the hold (`analysis/solr-2026-10-18/hold/`).
- Solvers are charged their corpus's estimate at start (`campaign_solver_live_pct` 50 %, measured before compaction):
  re-measure a solver's live set before lowering it.
- World depth > 0 (owner: unbounded in principle): the generation-1 study's path -- replays reproduce the seed's run
  constants, a cone sub-query answer cache, D2 redone with its review's fixes (`analysis/solr-2026-10-18/gen1/`,
  `resume/D2-REVIEW.txt`) -- before any depth > 0 default.
- The VM still renders each read-out page's whole closure before choosing what to send (~0.2 s per 20 MB).

**6. Open problems from the final rounds** (2026-10-13..16; each with its evidence, by the letter STATUS and the design
docs cite; the ones done since are gone from this list):
- **d. New-bug candidates:** 38 (SAT confirmed in the VM, native 0/10: the PULL replicas' getLeader hang); the lost
  watch -- a watch callback whose re-read fails with ConnectionLoss past ZkCmdExecutor's retries, session alive, only logs
  and never re-arms (`ZkStateReader.AliasesManager#process`, `StateWatcher#refreshAndWatch`), one bug behind solr-adhoc-40
  and -09 (both UNSAT today), JIRA has no report (SOLR-16257 differs). Each: realism, JIRA, STATUS,
  docs/checks/new-bugs.txt.
- **f. Producer-conjunct pruning in the flip query (after the group):** `FlipQuery#arm` asserts a handoff producer's whole
  path condition, so one guard's arm is another question in every upstream world (SC9-19 r13: 32 ids per arm, 7 or 1
  without the stated handoffs); keeping only the conjuncts sharing variables with the delivered term or the guard would
  make them one question -- a query design change, and what the depth bound stands in for.
- **g. Cleanup owed:** REPRODUCE's summary counts no VIEW_HOLD row (its jq reads ROOT/ANSWER/ORDER only).
- **o. A read-out page's header on the closing thread (follow-up of `solr-readout`, VM):** the owner thread reads each
  page's `complete` and `nextAfterEventId` (`SharedStateCapture#pageHeader`) by skipping every record before them with a
  JsonReader, about 4 MB/s on the Zero interpreter (SGF3-31: ~870 MB of record text on the closing threads, with the VM
  context held). The VM writing those two members before `locations` makes it a read of the page's head.
- **p. One writer id for two decodes in two runs (FB, 2026-10-13, not done):** a node's StateWatcher callback is
  identified by its anchor, the Overseer `setData` endpoint that fired it, and tick counts are not identity: in
  SGF3-bugs-snapshot-no-active the seed's decode of v5 of node0's `state.json` view and session 9e4cbffc's decode of
  v12 are both callbacks anchored on c6176901b30565df, one occurrence id 12eebcfee65f82ae, so one writer key
  (`ComposedFamilies#writer`, `Arms#stateArms`' one arm per writer occurrence) and one STATE slot id stand for two
  decodes of two runs. Within one session each decode had its own anchor (9e4cbffc: v4-v12, nine anchors), so no
  in-session alternative was lost there. Keying VIEW writers by (occurrence, version) re-keys `Arms#stateArms`,
  `ComposedFamilies#writer` (every VIEW writer's selector and assertion names: no case with a view family stays
  byte-identical), block granularity (`holdBrokenBlocks`) and the slot ids families are keyed by; a design of its own.
  Evidence: the sessions' `writes.jsonl` (VIEW `/collections/causynthSnapshot/state.json`, node0) and
  `/bigtemp/vnr3ne/analysis/solr-2026-10-12/fb-viewwriter/ab-probe2/candidate/solr-bugs-snapshot-no-active/COMPOSE/stderr.log`
  (PROBE lines).
- **q. Fewest clocks across paths (WF, 2026-10-13, not done):** `ClaimPolicy#leastClocks` keeps the fewest clock jumps
  within the witness's own path; a witness on another sat path might need fewer (fewer moved clocks, fewer native
  timing turns). Choosing among paths means a refinement per sat path; measured on PRE4-18406 before any build.
- **r. The exact in-force hook of a notification's publication (`solr-pubturn`):** its PUBLISH turn is taken when the
  watch callback ends (`MessageDoors#notified`), after `constructState`; what runs between the cluster state's write and
  the callback's end (`notifyStateWatchers` waking a `waitForState`, the update lock's release, `publishIfNewer`'s
  `notifyAll`) can pass the turn (IDENTITY §8).  Exact: a one-line `MessageDoors` hook where the view is in force -- right
  after `constructState` assigns `clusterState` (final9 :650, settling only a delivering thread's owed turns) and after
  `AliasesManager#publishIfNewer` sets `aliases` -- a new tree (final10), its natives and validation; only if a seed
  shows the window.
- **s. Arm-key redundancy (`solr-armkey`, parked 3bfdca7bc; the Z3S-18413 diagnosis of 2026-10-13 found each parent
  past the MIGRATE re-keying the same arm, ~235 parents by round 2):** the key naming the delivering world's whole fault-root
  valuation (`Corpus#handoffName`, `Arms#rootGuards`) re-asks one arm per parent world (Z3S-18413 up to 47 ids/arm;
  SGF3-adhoc-39 7.72, top 59). The fix tried (name only roots the question reads) folds questions FlipQuery still tells
  apart: roots pinned through other eligible writers, view decodes and own-run arms; earlier non-kept decisions,
  inherited flips' conjuncts and domain-less pinned roots. Needs a KeyGate-style check (re-key answered arms; no key covers
  both a SAT/ADMITTED and an UNSAT answer) before any merge. Review findings in the branch's history.
- **t. Container mutations the VM never sees (FB diagnosis, `solr-vmfp`):** a tracked map mutated with only concrete
  arguments, unguarded and with no callback, runs as plain bytecode (`symbolicMap.cpp:400-406`), and a thread with no
  activation never reaches the model (`cppInterpreter_zero.cpp:570`); containers carry no read-time version check
  (`sharedFieldVersions.hpp:76-80`, `containerSupport.cpp:1225`), so a later read joins a stale version silently
  (SGF3-adhoc-09 path 13: MAP 1368 read null at seq 5090, joined v3302 holding the collection; PRE4-adhoc-21 paths 5/13).
  Spurious PATH_SELF_CONTRADICTORY, possibly a false UNSAT.
- **v. Cross-run node spellings and message closes (`solr-portname`, parked b80976bb7):** a family closed for one
  session's delivery is reused for another's (`ComposedFamilies#closeMessages` keyed by consumer endpoints only), and
  another run's host:port literals decide arm compatibility (SGF3-adhoc-09 path 23). Review FIX FIRST: the respelling
  scope is taken from frame depth, so families (lowered after the path's frame closes) are respelled into the arm's own
  run; selectors keyed by group are shared by two closures of one group; CONFIRM would name respelled text by the arm's
  run; the regex has no digit boundary; unmatched spellings stay silently.
- **w. A sender's arm whose two values coincide where the receiver's differ** (PRE4-adhoc-21 path 6:
  message_family__6__6f5f76f8d017 binds two fields' handoffs equal, the receiving run compares them unequal): whether a
  sender's arm fits the receiver's state; open, not diagnosed further.
- **y. Snapshot's state.json delivery race (2026-10-16):** a SAT claim's WIRE edge from an Overseer state update to a
  reader of state.json content (message_arm over replica states) is checked, never held: SGF7SLOW19's CONFIRM refuted
  "WIRE 3f14387463b5d2bc: the model chose producer cda154d1fdd4aa38, the run paired 0908f39c6399d2e2" and WF5 the
  reverse. SGF7 on sgf20 passed by a witness that confirmed itself (realizedBy). A hold for a store read's delivery
  (as a VIEW_HOLD for a view) would make such claims confirmable.
- **z. A second static pass** (measured 2026-10-16): the static pass runs again over the demanded doors it chose (~95 s
  a case, a door shifts its method's unit indices).
- **aa. 18413's hand WIRE_FLOW rows** (`experiments/solr/solr-18413/communication-mappings.jsonl`): still needed -- the
  ZooKeeper chain keys state.json's `routingRules|a!|expireAt` but no field of `/overseer/queue`, so the expiry would
  cross the queue as a constant without them.
- **dd. The planner's heap after 64178b266:** spread over rows and expression tables, the per-session joins' keys, the
  shared-body texts, memo keys holding expression nodes the tables meant to hold weakly, the slot table (162 MB on
  adhoc-09) and the index keys (6-10 %). Sharding the corpus over hosts was parked by the owner (too large a change).
- **ee. The replay end peak:** a replay's heap use jumps 350 -> 890 MB in its last read (its session's publication);
  the admission now leaves room for four such ends (§0 of STATE §S). Making the publication itself smaller is open.

## The other systems

HBase (`system/hbase`, finished 2026-10-21), ZooKeeper (`system/zookeeper`, finished 2026-10-22) and HDFS
(`system/hdfs-liftlab`) keep their plans in their own TODO; the HBase and ZooKeeper steps this file held from 2026-10-08 (`hbase-startup`,
`hb-schedule` + `hb-sync`, the 2026-10-04 point lists) are superseded by those branches' own work.

## Cross-cutting (engine), when a system needs it

**The forced fatal arm (owner 2026-10-08; merged on `system/solr`, PIPELINE §7.10):** what is left -- `seedFlipsAfterForcedFlip`
was 0 in every Solr run of agent F2, so the seed path's anchor flips and open-arm asks may be deletable (decide on a round's
numbers); solr-adhoc-19's forced flip reads `clusterProperties`, parsed from ZooKeeper JSON.

**A transient ZooKeeper fault inside the retries (lead 2026-10-13, for later).** Every Solr ZooKeeper door stands at
`ZkCmdExecutor#retryOperation`'s boundary (SYMBOL-SCOPE §4.2): a planted ConnectionLoss escapes past the retries. The
transient world -- one ConnectionLoss inside the retries, retried, the retry meeting `NodeExists` (a create the first
attempt applied) or a duplicate sequential node -- is planted nowhere since makePath's hooks left its retry lambda
(`makepath-create-tree.patch`). A general in-retry door: the system names its retry wrapper (a doors.jsonl row), and a
door inside the wrapper's operation plants a fault on one attempt only, the wrapper retrying as it would.

**WIRE-CODEC (`wire-codec-p1` 3e9cb3182, a removed local branch; the system body carries none of it).** Resume only when a system's chain needs a
codec hole (a value carried inside an opaque payload); then rebase it onto the body, which deleted its runtime.

**VM performance.** The VM sends each expression node once per channel (STATUS open item 41). A plan budget should
be derived from the seed's measured cost.

**Timed-wait outcomes (owner 2026-10-09 discussion; the door is merged on system/solr 2026-10-11, the ORDER-row
model below is not built).** A guard decided by whether a timed wait
(`CountDownLatch#await(timeout)`, `waitForState`) timed out or was signalled: the TIMED_WAIT door makes the wait's outcome
a root, and the decider rule reads a helper that returns by whether the wait threw (`BooleanReturns#thrown`, solr-decider
2026-10-13: solr-adhoc-09's `DeleteReplicaCmd:278` through `waitForCoreNodeGone`'s catch to `waitForState`'s
`latch.await`); the signal itself still travels through JDK synchronization the VM does not track. A general model: a timed wait's outcome is a schedule choice -- the signal before or after the
timeout -- that a flip may ask and CONFIRM holds by an ORDER row. Needed for the external study's DeleteReplica candidate
(solr-adhoc-09; item 6d) beside the ZooKeeper READ doors.

**Decoded products' derived fields (agent Z2 2026-10-13; design (B) of
`/bigtemp/vnr3ne/analysis/solr-2026-10-12/design-z2-f2-decoded-state.md`).** A decode outside every region keeps its
minted leaves' symbols in the parsed tree, but a field the system derives from one there (`Replica.<init>`'s
`State.getState(String.valueOf(..).toUpperCase())`) is a plain constant: no VM model runs without the region's shadow
stack. Today the system weaves the classes that build its view in every case (`experiments/solr/system.sh`
`system_scope`), and the ZooKeeper chain keeps symbolic only the decodes the anchor rests on (SYMBOL-SCOPE §6.4). The general
fix: the adapter's decode bracket (`MessageDoors.decoded` / `jsonRead` of a fetch) opens a tracking activation, so every
decoded product's derived fields carry their expressions whatever the case's scope -- a VM/runtime change (a shadow
stack on a role thread, its writes attributed to the decoding occurrence) with an identity design first.

**A view's write at its publication (agent Z2 2026-10-13, deferred from PUBLISH).** A node's VIEW write is stated at
the decode (`MessageDoors#decode`), while what a read observes is the object its node published, which a pairing's
hold or a PUBLISH turn may defer past it: the row order and the observed version can disagree (SGF2
snapshot-no-active: v8's VIEW write before a read that observed v7). Stating the write at the publication (the
door's synchronous publish, the publisher's apply; the decode only for a view no door publishes) aligns them; it
moves every pairing's VIEW rows, so it is an identity change of its own, with a gate over the Solr pairing cases.
