# TODO: HDFS finished; Solr ended; HBase in progress (handover 2026-10-19 night)

Order:
1. HDFS is finished (STATE §0): its follow-up items below are optional engine work, done when a later system needs
   them or before a clean final acceptance run.
2. Solr: the rewrite and its final round SGF9 are done (2026-10-19, section "Solr: after SGF9"); what is left there is
   optional: the cases owed a run on the fixed engine, and the speed items with their evidence.
3. HBase: the current work (section "HBase", item 1 is the next runs in order); stopped by the owner on 2026-10-19
   23:10 for a handover to another agent.
4. ZooKeeper.

The owner: "hdfs所有的case跑完为一组，不要有回归。然后就到另一个系统". Each system is finished when every one of its
checks has an exported `.smt` that is right (SAT confirmed, or UNSAT at the fixed point) and every known bug of it
passes. Branch, tree and path details are in [STATE.md](STATE.md); every check with its state in
[../checks/README.md](../checks/README.md) and its reading in [../STATUS.md](../STATUS.md); commands in
[OPERATIONS.md](OPERATIONS.md); speed and the cluster in [../design/PERFORMANCE.md](../design/PERFORMANCE.md).

## HDFS (finished: `system/hdfs` 39 cases, `system/hdfs1` 7; trees r7, r7-21, r8, 11741-r6 = the fork's `graphchecker/*` branches; image `vm-hg5`)

46 of 46 cases closed with a hand-read `.smt` (STATUS "HDFS checks"); no new bug; every case ran alone on the ten
lifts for its time breakdown (EX1, PERFORMANCE §6). What is left is the general work the
workarounds stand in for, the defects the session found, and the cleanup. None of it reopens a closed case unless a
change alters its formula; any engine change below reruns the affected cases on `system/hdfs1` (one change per round,
RULES "Lock, then one change at a time").

### 1. The two-phase final acceptance run (owner 2026-10-06, for later)
For one clean run of all 46 on one body (once the items below are in or declined): (1) the ~36 short cases a few at a
time (6-8 concurrent: their time is serial SEED, recording and seed replay, so exclusivity buys them little); (2) the
deep closures (11741 08 09 05 06 11 14, 07) one at a time with the whole cluster (their cost is hundreds of obligation
replays, which fan out: 09 has 653 verdicts over 9 tasks and 7 regions). Expected ~4-5 h in all versus ~9-10 h with
every case exclusive. Note: the 39 cases of `system/hdfs` ran on the locked body, which lacks codec capture, open
arms, the wait deadline and the open-arm keys; a run of them on `system/hdfs1` is that final run's first check.
11741 needs `CASE_TIMEOUT_SECONDS=14400`.

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
  PERFORMANCE §5 item 0). Live (`/bigtemp/vnr3ne/gc-out/solr-incr-plan`): INC1-adhoc-09 UNSAT_CLOSED as EX1,
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

## Solr: after SGF9 (2026-10-19) -- the current plan; the Solr sections below are history

Read [START-HERE.md](START-HERE.md) and STATE.md §S first. `system/solr` (pushed) holds the rewrite and every fix the
final round SGF9 found; the owner ended the round on 2026-10-19 with 14, 07 and 31 not rerun. Evidence is under
`/bigtemp/vnr3ne/analysis/solr-2026-10-18/final9/` (named per item). Merge each branch into `solr-int`
(`/bigtemp/vnr3ne/wt/gc-solr-merge`), gate it (mvn package with tests + `src/test/shell/run_engine_campaign_helpers_test.sh`
on an idle host), fast-forward `system/solr` (`/bigtemp/vnr3ne/wt/gc-solr`); push only with the owner's OK.

**1. Cases owed a run on the current `system/solr`** (each alone, the round driver of START-HERE §3; budget 21600 s for
the big ones). None of the three fixes below has run on a case yet, so the first run of each is also its check:
- 14, 07, 31: never finished on the rewritten engine (SGF8OOM; SGF8 07 composed 1 of 309, all 309 offline; SGF9KILLED-31).
- 39, 19, 13, 09: ended with GROW re-run sessions no round planned over (4, 18, 8, 6; 09 also dropped 3 re-runs before they
  ran): the fixed point beside unlanded re-runs, reverted in b9ecc0ba2 (`c39b/FINDINGS.txt`; 39's SGF8 run planned 77
  obligations over them, 48 ADMITTED = paths). 05, 10, 21 have 1 such session each.
- 05: its decide answered nothing in the round (every scoped z3 out of memory at the fixed 1024 MB pair slot); the z3 slot
  fix (solr-z3slot) re-decided it offline from its frozen inputs (`z3slot/`, STATUS row). A full rerun needs ~4 h
  (exploration 10701 s).

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
  composes 28 of 44 and still decides NO_SUPPORTED_WITNESS (`c19/FINDINGS.txt`). COMPOSE now places a cell by another
  node's reading of the same JVM clock (`Composer#nearestAnchor`; HZ17-mat 2 -> 112 of 114 paths composed); 19 not rerun on it.
- A free leaf for an unmodeled operation in a fatal arm the recording did not take is held to its recording where
  nothing it rests on moved (`Composer#hold`, PIPELINE §8; HP8-15's seed path was claimed FORMULA_SAT moving nothing);
  an enum compare over a chain of reads none of which moves is the name its last writer stored, written or not
  (`SmtLowering#enumRead`: HP8-15's 213 phi leaves). Left on HP8-15: 245 leaves in the path condition, `Procedure#isSuccess`
  over `Procedure.state` at a version no write row states that the anchor's family re-pairs: held OWN at the read's
  REF concrete value, so the writers' enum names are `ARM_SORT_MISMATCH` and no world re-pairs that read; an OWN enum read
  could state the name its observed version carries instead (not built: no case needs that re-pairing yet).
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

**6. Cleanup.** Done 2026-10-19: the rewrite's and the round's worktrees (their branches kept: solr-growshape is the one
unmerged that TODO names) and the Solr snapshots sgf9*, sgf28-41, can9a/b, growpipe1, nfs2. Left: the older snapshots
under `~/gc-run` from before the Solr final rounds (z2-*, zk*, rx*, sbm*, ...: check `tools/lib/alive.sh` first) and the
fresh-clone check's `/bigtemp/vnr3ne/wt/fork-check6-gc`, `fork-trees6`; the analysis dirs keep their evidence.

**7. Next system: HBase** (owner's order). Before its cases, measure in the Zero VM what HDFS costs a workload: a typical
HBase unit test with MiniDFSCluster against a local filesystem (`hbase.rootdir=file://`, `hbase.wal.provider=filesystem`,
`hbase.unsafe.stream.capability.enforce=false`); checks whose cause lies in HDFS interplay can run HDFS as a native
process outside the VM, its client calls a door (the `HADOOP_IPC`/`HDFS_DATA_TRANSFER` catalog entries exist). Keep
ZooKeeper inside the VM: its doors carry the coordination bugs.

## Solr history: the final round SGF8 after the optimization batch (2026-10-16; superseded by "Solr: the rewrite" above)

**Read first:**
1. STATE.md §S.
2. `/bigtemp/vnr3ne/analysis/solr-2026-10-15/HANDOVER-2026-10-15.md`: the lead's handover, with rulings, results, code state, the open bugs and the resume commands.
3. `HANDOVER-agents.md` beside it: the design per area (WF: ZooKeeper chain and PLAN; SV: solver lanes and cone; SN: runtime and replay speed; RP: schedule and CONFIRM holds; PL: GROW and cases).
4. This section.
5. STATUS "Solr checks".

The lead's session logs are the memory files `lead-session-2026-10-13-solr` and `lead-session-2026-10-15b-solr`
(2026-10-15 night: the blockers fixed, the round on the final code).

**Goal** (owner, restated 2026-10-15): finish the remaining cases of the final round (SGF8 since 2026-10-16) and report each case's time breakdown. The tool is `analysis/solr-2026-10-14/final-stats.py SGF7` and `SGF8`; each case runs alone on the cluster.
- **Bug checks:** SAT + CONFIRM + native ≥1/10 with the bug's own chain.
- **Study checks:** a solver SAT or UNSAT, or a named bound.
- **Standard, relaxed** (owner 2026-10-15):
  - a roughly-right `.smt` with a light reading;
  - best-effort merge of path conditions: problem parts are dropped, never blocking;
  - prefer refusing or dropping early to more work;
  - never rerun a case with a result, except the >1 h ones on the new code.
- **ZooKeeper:** only the (znode, field) the causal trace puts on the anchor's chain are symbolic.
- **Pushing:** the fork `JHSUYU/solr` `graphchecker/solr-checks` may be pushed without asking, never apache. Pushing GraphChecker needs the owner.

### 0. What `system/solr` holds (merged, green: mvn + the shell test)

Merged before 2026-10-11: the served incremental planner; the forced fatal arm, the VM's `Collectors.toMap` and enum
models; confirm-first; the owner's FP rule; the Solr body (HTTP send in `executeMethod`, stall rules); the closure's
precision (confinement by causal context); the String-shadow VM fix (`vm-force5`); native order-holding; a growing
round's proposals queued; `report.py`'s mechanisms for the 8 bug checks.

Merged 2026-10-11/12 (this session; each reviewed by a read-only review agent before the merge, findings fixed):
- `solr-body` 873fdaa20: the store READ turn.
- `solr-study` 01eda3dc0: force2's loop bound, way guard and passable asserts with both reviews' fixes; the Root:WAKE rule
  (39's seed 3/3, 31's 2/2); D1b; an anchor reached only by an admitted session (`RestsOn#reached`); deciders through a
  lambda; a fixed-count loop's own K_L.
- e53e88bae (lead): the realized order names events by stable contexts (`contract.StableEventNames`).
- `solr-study2` 70227b2cc: the realized order held only on the claim's cone + one-hop producers (18413 native 0 -> 10/10;
  restore stays 10/10); 05's loop bounds; trees.tsv/REPRODUCE §6 drafts.
- `solr-zk-state` (Z1) 184995cdb: ZooKeeper store versions and provenance (store rows keyed occurrence|seq|location|
  version, path lives `<path>#<n>`, provenance skip rows, decode waits for an in-flight write), CAS chains, batching turns,
  turn-wide doors, STORE reads as stated rows CONFIRM compares by writer, the engine's own output and logging calls under
  the VM's pause (`ConcolicVmBroker#asEngineWork`, never loading the broker), vm-force6 reverted. 18413 seed 7 min.
- `solr-moved-member` 8c343eba3: a member a replay ran on another node under its context shape -> ADDRESS_UNSTABLE
  DIAGNOSTIC, not BLOCKING.
- `solr-timed-wait` d90eb5a63: the TIMED_WAIT door (FAULT root at a timed wait whose outcome the slice reads; a planted
  timeout takes only where the real call could time out); GROW of a door invocation only a flipped world made
  (UNPLANNED_INPUT, whole-plan generations, k <= 4 counted in `bounded`, native plant per invocation).
- `solr-grow-swap` d6bd54203: GROW's swap waits while a witness confirmation is owed; a confirmed witness drops pending
  re-runs; the aside by copy (NFS).

Image then: `/bigtemp/vnr3ne/vm-force5/j2sdk-image` (today `vm-force8`, §1). Canaries on the merged body: IB2 (301871532) 18406/18413/migrate PASS
native 10/10; TW5 (timed-wait head, tree z1-trees) PASS native 10/10.

Merged 2026-10-12/13 (lead; through `solr-int`, each merge gated; the owner's order zk-doors -> explore2 -> zk2 kept):
- `solr-zk-doors` (READ doors + R4), edc62b76b.
- `solr-explore2` + `solr-key6` (EX): arm keys named by Tarjan, (B) handoff sets, (C6) a member's store-content handoffs
  as reads, the task's own line names message handoffs only (item 1), a faithful NOT_ADMITTED alone settles an arm, a
  query refused at the arm settles the arm (ARM_REFUSED), handoff/read names kept as digests once closed, -Xss512m on
  engine JVMs; lowering: a frame holds each unbound value once, long texts (> 2048 chars) as define-funs, a view leaf
  lowered once per memo and cased once per read; the world-depth bound `region_path_max_world_depth` with the study
  cases' policy in `experiments/solr/solr-adhoc/case.sh` (named BOUNDED in `campaign_bounds`).
- `solr-zk2` (Z2): content leaves of unattested producers settled by their own run's export (EXPORTED, CONSTANT,
  BOUNDED `daemon_tick_bound`); String.split elements, String.valueOf, enum compare lowered; rows ordered (seq, tie)
  (`contract.RowOrder`); the view pairing defers the node's publication (a') (`MessageDoors#publishing`, per-path
  queue, VIEW_HOLD_MAX = 3000 ms recorded x slowdown, `view_hold_max` in `campaign_bounds`); the anchor's work past the
  path is no producer for it (189a797b6); another version's content rests on the view's choice of it, an unsendable
  version unpaired (2d07350c5; merged memo-safe by the lead, ce92cb6a6: a frame carries what it lowered inside a case,
  a symbol rests on its innermost case's choice).
- `solr-solve`: the solve's two lanes (now `solr-hardlane`: the hard lane is z3 alone over the first ask's query in a
  corpus-free JVM; no question is answered in a corpus JVM of its own; a cold host's charge goes to its solver).
- `solr-str`: String.toLowerCase/toUpperCase lowered exactly over ASCII.
- `solr-str2`: every String arity the VM emits with an exact SMT-LIB form z3 decides: `startsWith(p, off)` (39's
  59 refused paths), `indexOf`/`lastIndexOf` with a from index and code points, `regionMatches`, `compareTo`,
  `subSequence`, `equalsIgnoreCase` with a literal side; the rest refused by name (VM.md, String row).
- Lead: an engine JVM is charged its footprint H + H/16 + 384 MB; a stream replay its typical peak (p90 after
  eight); `launch-round.sh` passes CASE_TIMEOUT_SECONDS, PRUNE and CAUSYNTH_CAMPAIGN_STOP_AFTER to the heads.

Merged 2026-10-13 morning (lead, through `solr-int`, each gated; SGF on 12cd346d9 found the defects they fix):
- `solr-zk3` (Z2) f904ab427: a String cell read at REF sort is its string's reference (`string_ref`, injective, never
  null) and reboxes to its cell -- the VM states an enum constant by its name, so `CollectionAction.get`'s symbolic-key
  lookup made every Overseer command path self-contradictory (false UNSATs; SGF-reindex).
- `solr-str2` (ST) c403c41a4: every String operation the VM carries with an exact SMT-LIB form (startsWith/indexOf/
  lastIndexOf with offsets, regionMatches, compareTo, subSequence, equalsIgnoreCase against a literal); the rest refused
  by name (VM.md's String row).
- `solr-lockleak` (EX) ec343e291: STORE_ITEM_PRODUCER (a demanded store writer's starting items' senders are value
  producers); the VM's base pause, image `/bigtemp/vnr3ne/vm-force8/j2sdk-image` (a doors-only occurrence's frames keep
  their tracking, so a door in a callee decides; shadows cleared when the pause is retaken; a window outside an
  observation bracket an ENGINE_FAULT). Both reviewed (`/bigtemp/vnr3ne/analysis/solr-2026-10-12/review-*.md`), fixed.
  The jar refuses images before vm-force7.
- `solr-sessions` (EX) c5ddff24a: a planted SessionExpired is a real expiry of the door's session at its server (the
  system's expirer, `runtime.Sessions`; the Solr tree registers it), else refused by name.
- `solr-native-charge` (EX) df3bfbd41: a native run is charged 130 % of its recording's peak; onlift never picks lift11.
- `solr-zk4` (Z2) bfada52ac: snapshot-no-active's scope (solrj ClusterState, DocCollection, Slice, Replica) and world
  depth 0, named BOUNDED.
- `solr-arm39` (ST) 181d4cf3a: a message's senders are judged against the path's own world at every depth, by flips and
  by the pins their arms carry; none compatible is UNPRODUCIBLE_ANSWER by name.

Merged 2026-10-13 midday (lead, gated):
- `solr-ztimeout` (EX) 2e02f345f: ZooKeeper doors fault ConnectionLoss and SessionExpired only (the 3.6.2 client never
  raises OperationTimeout; RequestTimeout only with zookeeper.request.timeout > 0); every Solr ZK door sits at the retry
  boundary, makePath through create on final9.
- `solr-plancost` (EX) 14753dafb: planner caching and indexing, byte-identical plans on 4 corpora (96 files).
- `solr-f9docs` (ST): the tree gc/solr-final9; `solr-sc-newbug` (SC): new-bugs #14 (solr-adhoc-38); `solr-qwdocs` (ST):
  the Overseer idle-wait hazard (fixed in final9).

Merged 2026-10-13 afternoon (lead, through `solr-int`, each gated; system/solr fast-forwarded after the gates):
- `solr-zk5` (Z2) bb2a20b30: a node's view publication is a recorded schedule event PUBLISH (the seed follows the
  recording; a hold still wins); one store leaf one value at any scalar sort; PAIRING_OVERRIDDEN; COMPOSE gives no version
  choice to a view no hook holds; every claim CONFIRM does not confirm is excluded (refuted|undecided). Gate: L3Z-18413
  PASS 2133 s, native 10/10 (Z3S-18413's growth was not zk5's: below, §3n).
- `solr-native-claim` 7c376da8e + `solr-confirm-spell` e2605ff19 (SC): a native run holds a hand-off pool's claimed task
  where it runs unless the task serves a queue; CONFIRM compares a WIRE value through each run's node spellings. Gates:
  L3C-18413 PASS native 10/10, L3C-restore PASS 8/10 (plant without ORDER rows; two runs stalled after the failover),
  L3C-reindex (native >= 1/10, no Runner key in `servingTasks`).
- `solr-replaybound` (EX) bdc347713: a replay killed past replay_timeout_s answers nothing; a flip killed twice is BOUNDED
  by name. `solr-forcebound` (FB) 015501d6b: the FORCE run likewise (its question named by its flip).
- Hosts lift02-05 (owner 2026-10-13) in `LIFTS` and `launch.sh`; lift01 lacks `/bigtemp`.

Merged 2026-10-13 evening (lead, through `solr-int`, each reviewed by a read-only agent where it touches the schedule,
COMPOSE or the ledger, and gated); found by the SGF3 runs on the code before them (SGF3 is a preview; the final round is
SGF4 on all of them):
- `solr-exposeid` (FB) cc9a3ef5c: an obligation asked again under its id has a worker and a session per ask; every pairing
  of an ask with its artifacts goes by session (SGF3-adhoc-21 died on "no one worker with a focus row").
- `solr-witfirst` (WF) 7ec64b960: a planner round runs in its own lane over frozen inputs; a landed witness is attempted
  within one gate step (Z3S-18413's witness had waited ~70 min behind a round).
- `solr-readout` (RO) 61a9661bf + 8b5164611: a read-out envelope seen again unchanged is filed as its held decoding
  (SGF3-adhoc-31's seed was decode-bound, drifted, never reached its target; now it does).
- offline-ab passes the case's system doors file to every stage (FB, 3b8a3de7b); solr-adhoc-39 at world depth 0.
- `solr-viewwriter` (FB) 8d1e434d7: a run writer with no selector holds its location by the observed arm, named;
  round-verify prints HOLD:<n>.
- `solr-z3mem` (WF) e0b546c6d: every z3 under memory_max_size, charged on the ledger (SGF3-adhoc-13's COMPOSE z3 had
  swapped lift12).
- `solr-pubturn` (PB) 48e76fde4: a view's PUBLISH turn is settled when its publication is in force (SGF3-bugs-snapshot's
  seed read node0's view at v7 -> SEED_OBSERVED_FATAL).
- `solr-margin` (WF) cee108ef1: a witness's clock margin sits on the jump (PRE4-18406's 2-clock witness kept 1 ns, native
  0/10).

### 1. Branches (2026-10-15 handover)

Every agent branch of 2026-10-15 is merged into `solr-int`; each agent's section in
`/bigtemp/vnr3ne/analysis/solr-2026-10-15/HANDOVER-agents.md` lists its shas. Unmerged leftovers:
- `solr-finalreuse` worktree: committed and merged; its WIP worktree can go.
- `solr-snapshot-pin`: reset to 6fcbd8b80. The pin was withdrawn, because the enclosing BackupCmd.call
  occurrence observes the target.
- Older parked branches (`solr-vmfp`, `solr-armkey`, `solr-portname`): unchanged, after the round.

Solr tree: `gc/solr-zktrace` 8fde6b812c (`/bigtemp/vnr3ne/wt/lucene-solr-zktrace`,
`GC_TREES=/bigtemp/vnr3ne/wt/sg3i-trees`) = final9 0ce3deafed + SolrZkClient's store-read door and the
watcher's path/type. 17/17 natives. The kept SGF7 results ran on final9 (`sg3h-trees`); never rebuild either.

### 2. ZooKeeper READ doors (owner priority 2026-10-09)

Merged (§0). The external study's lost-watch failure (a watch callback whose re-read fails with ConnectionLoss past
ZkCmdExecutor's retries, session alive, only logs and never re-arms: `ZkStateReader.AliasesManager#process`,
`StateWatcher#refreshAndWatch`) is one bug behind two checks, solr-adhoc-40 and solr-adhoc-09; JIRA has no report
(SOLR-16257 differs). A confirmed witness of either by a READ-door fault on the re-read is that candidate rediscovered.

### 3. Open problems (each with its evidence)

- **a. lock-leak's chain:** SG3I (int7 + final4) went SAT confirmed by a SessionExpired at the state writer's setData plus
  a ~160 s hold of node1's view, native 0/10: a false positive (the old blocking hold under the refresh lock, and
  CausynthBounds stretching modifyCollection's 30 s wait to 6 h; the (a') hold's VIEW_HOLD_MAX excludes it). The bug's
  chain was never planned: markTaskAsRunning's running-map put is `SolrZkClient.makePath` in node0's queue tick
  (`Root:OVERSEER_TASK_QUEUE`), the message that starts the async Runner, and the Runner was admitted only as a control
  producer, whose starting message's doors are not asked (`ClosurePlanner` "a control producer contributes no value").
  The Runner is a value producer: its task message's empty readOnly removes the property in v8 (SOLR-12507). Its
  flip is a ConnectionLoss past `ZkCmdExecutor`'s retries at `create`'s door, which makePath reaches through `create`
  on `gc/solr-final9` (`makepath-create-tree.patch`; SGF2's witness was an OperationTimeout inside makePath's retry
  lambda, a kind the 3.6.2 client never raises, now no kind; live gate on final9: lock-leak and 38). Analysis
  `/bigtemp/vnr3ne/analysis/solr-2026-10-12/readings/lock-leak-SG3I.md`; pre-reading `.../solr-2026-10-11/readings/lock-leak.md`.
- **b. 18413:** both SG3G/SG3H refutations fixed (§0, Z2); CONFIRM watch: a seed arm with a Lost-context consumer and arms
  whose sites carry queue sequence names (qn-...) can shift identity between runs.
- **c. Seed drift of 31 and 05: DONE 2026-10-16 (with §3x).** The Overseer's `peekElements` WAKE turns: a
  timed-wait loop's events take their turn family's slots and its reads none (`ScheduleLog#turnFamily`, 19ae623a7),
  and the tree `gc/solr-zktrace2` 12d23091d1 takes the two timing choices out (the test client's live nodes in node
  order; an unbatched Overseer's queue removal in its message's own turn). 31's client polls remain (§3cc). Evidence of
  the old experiments `/bigtemp/vnr3ne/gc-out/solr-sc`; of the fix `gc-out/turnfamily-ab`, `gc-out/tfj-ab`.
- **d. New-bug candidates:** 38 (SAT confirmed, native 0/10 named: native order beyond the fatal cone); the lost watch
  (§2); 19's stale cluster-property view at core creation if SGF confirms it. Each: realism, JIRA, STATUS,
  docs/checks/new-bugs.txt.
- **e. 14:** its forced phi is a constant (accepted); a ZooKeeper path's liveness and a server-side session-expiry root
  are not modelled (`.../solr-2026-10-12/readings/14.md`).
- **f. Producer-conjunct pruning in the flip query (after the group):** `FlipQuery#arm` asserts a handoff producer's whole
  path condition, so one guard's arm is another question in every upstream world (SC9-19 r13: 32 ids per arm, 7 or 1
  without the stated handoffs); keeping only the conjuncts sharing variables with the delivered term or the guard would
  make them one question -- a query design change, and what the depth bound stands in for.
- **g. Cleanup owed:** REPRODUCE's summary counts no VIEW_HOLD row (its jq reads ROOT/ANSWER/ORDER only).
- **h. Timed tests:** the suites keep no timing-sensitive case (test cut 2026-10-18); what stays timed has seconds of
  margin (STREAM-1's 3 s LONG obligation, the REPLAY-BOUND rows' 1-5 s bounds, SOLVER-SERVICE's idle end).

- **i. The Overseer's idle wait: DONE in `gc/solr-final9` (cd98d779dc).** SGF2's reindex seed recording stalled
  because a missed child watch of `/overseer/queue` parked the never-timeout idle wait for good (evidence
  `/bigtemp/vnr3ne/gc-out/solr/accept-SGF2-bugs-reindex-cleanup`, schedule seq 938-963, the dump in
  `logs/solr-bugs-reindex-cleanup.log`); the idle hunk is reverted to stock's 3 s timeout (it alone had moved nothing,
  SC8/SC10) and the batching-0 hunk stays. If 05's seed drift comes back on final9: `ZkDistributedQueue#peekElements`
  never parks without an armed child watcher (under `updateLock`, if `watcherCount == 0` set `isDirty` and loop),
  automatic cluster only.

- **j. Replay timeouts settled flips (EX, `solr-replaybound`):** `Frontier.consume` counted a NOT_ADMITTED from a killed
  replay as a world-only answer; two of them settled the flip ("answered NOT_ADMITTED twice in its own world"), and
  the run published a clean UNSAT_CLOSED (EXZ1-38: 24 such flips, the expected witness among them).
- **k. CONFIRM compared node addresses as text (SC, `solr-confirm-spell`):** a WIRE value naming a node by its
  host:port refuted when the confirm run's port differed (NC3-reindex attempt 0000).
- **l. 38's interleaving:** the witness exists only where the PULL replicas register after the leader's publish fault;
  on final9's recording two registered before it and the third hung in getLeader (the native 0/10 hang), so every replay
  of that flip timed out. An ORDER variant of those creates is not asked by the planner; if SGF3 records the same
  order, 38 stands on its SC5/SGF2 SAT with this note.
- **m. Study cases' formula size:** with content capture, a satisfiable formula takes minutes per z3 run (reindex
  attempt 0000: 1459 s COMPOSE, the witness solves 4-9 min; 39's seed path self-check times out); a case's COMPOSE can
  eat its budget (13 in SGF2).
- **n. Arm-key redundancy (Z3S-18413 diagnosis, 2026-10-13):** not solr-zk5's: the seeds match (22710 vs 22402 rows), no
  PUBLISH or ORDER site is among the obligations, `leafEquals` is COMPOSE's only. Z3S planned with ~235 parents by round 2
  (SGF2 at most 2): each parent past the MIGRATE re-keys the same arm (inferred: the `expireAt` clock value in
  `Corpus#inputShape`), and its witness waited behind the round-2 planner. Packages `solr-armkey`, `solr-witfirst` (§1).
  Evidence `/bigtemp/vnr3ne/gc-out/solr-zk2/accept-Z3S-18413`.
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
- **s. Arm-key redundancy (`solr-armkey`, parked 3bfdca7bc):** the key naming the delivering world's whole fault-root
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
- **u. SEED's static pass looked nondeterministic: a harness defect, fixed.** The divergent A/B pairs (07: 2803 vs 609
  scope-map rows) were batches stopped mid-way: `offline-ab.sh ab_stage_seed_static`'s growth loop ended on a bare
  `|| break` and left the last pass's exit=0 over a half-grown scope; completed runs of one jar are byte-identical and the
  live campaigns' scope maps agree across reruns (`/bigtemp/vnr3ne/analysis/solr-2026-10-13/static-nondet/evidence.txt`).
  The stage is now `exit=cut step=<step>` unless the loop reached its fixpoint.
- **v. Cross-run node spellings and message closes (`solr-portname`, parked b80976bb7):** a family closed for one
  session's delivery is reused for another's (`ComposedFamilies#closeMessages` keyed by consumer endpoints only), and
  another run's host:port literals decide arm compatibility (SGF3-adhoc-09 path 23). Review FIX FIRST: the respelling
  scope is taken from frame depth, so families (lowered after the path's frame closes) are respelled into the arm's own
  run; selectors keyed by group are shared by two closures of one group; CONFIRM would name respelled text by the arm's
  run; the regex has no digit boundary; unmatched spellings stay silently.
- **w. A sender's arm whose two values coincide where the receiver's differ** (PRE4-adhoc-21 path 6:
  message_family__6__6f5f76f8d017 binds two fields' handoffs equal, the receiving run compares them unequal): whether a
  sender's arm fits the receiver's state; open, not diagnosed further.

- **r. The exact in-force hook of a notification's publication (`solr-pubturn`):** its PUBLISH turn is taken when the
  watch callback ends (`MessageDoors#notified`), after `constructState`; what runs between the cluster state's write and
  the callback's end (`notifyStateWatchers` waking a `waitForState`, the update lock's release, `publishIfNewer`'s
  `notifyAll`) can pass the turn (IDENTITY §8).  Exact: a one-line `MessageDoors` hook where the view is in force -- right
  after `constructState` assigns `clusterState` (final9 :650, settling only a delivering thread's owed turns) and after
  `AliasesManager#publishIfNewer` sets `aliases` -- a new tree (final10), its natives and validation; only if a seed
  shows the window.

- **x. The Overseer-queue seed drift: DONE 2026-10-16** (owner-approved rule, §3c): adhoc-10's seed replay 107 -> 22-33
  stalls, window 574 -> 407-489 s, recorded occurrences reproduced 727 -> 860-912 of ~1120; a focused replay 446 ->
  350 s.
- **y. Snapshot's state.json delivery race (2026-10-16):** a SAT claim's WIRE edge from an Overseer state update to a
  reader of state.json content (message_arm over replica states) is checked, never held: SGF7SLOW19's CONFIRM refuted
  "WIRE 3f14387463b5d2bc: the model chose producer cda154d1fdd4aa38, the run paired 0908f39c6399d2e2" and WF5 the
  reverse. SGF7 on sgf20 passed by a witness that confirmed itself (realizedBy). A hold for a store read's delivery
  (as a VIEW_HOLD for a view) would make such claims confirmable.
- **z. Smaller costs measured 2026-10-16:** the static pass runs again over the demanded doors it chose (~95 s a case,
  a door shifts its method's unit indices), open. Done: the composer's start heap (its corpus's) and its roots'
  domains (an index over the corpus: adhoc-10 891 -> 52 s).
- **aa. 18413's hand WIRE_FLOW rows** (`experiments/solr/solr-18413/communication-mappings.jsonl`): still needed -- the
  ZooKeeper chain keys state.json's `routingRules|a!|expireAt` but no field of `/overseer/queue`, so the expiry would
  cross the queue as a constant without them.

- **bb. A timed-wait turn's number in CONFIRM and the native plant: done 2026-10-18** (solr-stream2, OPTIMIZATIONS
  2.4): both by the turn family, the replay's rule.
- **cc. 31's test-client polls: done 2026-10-18** (solr-stream2, OPTIMIZATIONS 2.3): a write waiting only behind READ
  slots stands a grace, not the CEILING deferral (16 s -> 2 s a read).
- **dd. The planner's heap after 64178b266:** spread over rows and expression tables, the per-session joins' keys, the
  shared-body texts, memo keys holding expression nodes the tables meant to hold weakly, the slot table (162 MB on
  adhoc-09) and the index keys (6-10 %). Sharding the corpus over hosts was parked by the owner (too large a change).
- **ee. The replay end peak:** a replay's heap use jumps 350 -> 890 MB in its last read (its session's publication);
  the admission now leaves room for four such ends (§0 of STATE §S). Making the publication itself smaller is open.

### 4. The final rounds SGF7 and SGF8 and the fork (2026-10-14/16)

0. **SGF7 results** (`gc-out/solr/accept-SGF7-<case>`; readings in `analysis/solr-2026-10-14/final-readings.md`):

   | case | wall (s) | result |
   | --- | ---: | --- |
   | 18406 | 828 | SAT, native 10/10 |
   | 18413 | 2019 | SAT, confirmed, native 10/10 |
   | migrate | 699 | SAT, native 10/10 |
   | restore | 610 | SAT, native 10/10 |
   | lock-leak | 875 | SAT, native 10/10 |
   | tra | 943 | SAT, native 10/10 |
   | reindex | 1113 | SAT, native 10/10 |
   | snapshot-no-active | 878 | SAT, confirmed, native 10/10 |
   | adhoc-38 | 1222 | SAT, VM-confirmed, native 0/10 |
   | adhoc-09 | 6887 | UNSAT_CLOSED |

   Evidence, not results: adhoc-10 SGF7 (10228 s) and SGF7B (6086 s, the pooled compose), adhoc-40 SGF7 (killed at its
   budget, no claim), the stopped runs `accept-SGF7OPEN16-18413`, `SGF7SLOW17-18413`, `SGF7HOLD18-18413`,
   `SGF7SLOW19-bugs-snapshot-no-active`, `SGF7GC22/23-adhoc-10`.
1. **SGF8** (running): 21 19 14 13 10 40 39 05 07 31 on `~/gc-run/sgf28` = 64178b266 and `sg3j-trees`, 7200 s each.
2. **Resume:**
   - gate solr-int, then ff system/solr from inside `wt/gc-solr`;
   - build a snapshot with `tools/lib/worktree-add.sh ~/gc-run/sgfNN <sha> --detach` and `onlift` mvn;
   - run the driver detached on lift06: `analysis/solr-2026-10-16/final-seq5.sh <snap> <trees> lift06 <case:7200> ...`
     (it skips a case whose SGF8 run has a verdict);
   - per case: `timeline.py`, a light `smt-legend.py` reading, a row in `final-readings.md`, `final-stats.py SGF8`.
3. **The fork:** `graphchecker/solr-checks` = `gc/solr-zktrace2` 12d23091d1 (pushed 2026-10-16; 17/17 natives on sg3j).
   The fresh-clone check of 8fde6b812c passed (`analysis/solr-2026-10-16/fork-check4.sh`: 17/17, 20/20 VALID); one of
   12d23091d1 is owed once the round ends (it needs the pool).

### 5. Where things live

- Handover: `/bigtemp/vnr3ne/analysis/solr-2026-10-12/HANDOVER-2026-10-13.md`; the lead's notes, readings, reviews,
  designs and scripts (launch.sh, watch-remote.sh, live.txt) in the same directory; memory `lead-session-2026-10-12-solr`.
- Rounds: `/bigtemp/vnr3ne/gc-out/solr` (SGF-*, SGF2-*, SGF2R-*: the lead's); `gc-out/solr-zt` (EX, EXZ1-*),
  `gc-out/solr-zk2` (Z2, Z3*), `gc-out/solr-sc` (SC, NC*, SC*), `gc-out/solr-sg3` (ST: natives, fork checks),
  `gc-out/solr-explore2` (EX earlier).
- Snapshots: `~/gc-run/sgf2` (SGF2's code, c3e446e38), `~/gc-run/ex-zt1` (EXZ1), `~/gc-run/z2-37` (solr-zk5 R2b),
  `~/gc-run/nc1..nc3` (SC); older int*/sgf/z2-*/ll* can go after a pgrep on every lift.
- Trees (GC_TREES dirs, each a `lucene-solr-checks` link): `sg3h-trees` -> final9 (the cases' tree), `sg3g-trees` ->
  final8, `sg3f-trees` -> final7, `sg3e-trees` -> final5 (the fork's today). A case.sh `repo=` resolves under GC_TREES;
  the default `/bigtemp/vnr3ne/wt/lucene-solr-checks` is an old directory, never the one to run.

## HBase (`system/hbase`; stopped by the owner 2026-10-19 23:10 for a handover -- the current plan)

Read [START-HERE.md](START-HERE.md) and [STATE.md](STATE.md) §H first; every case's state is `docs/checks/HBASE.md` §E,
each agent's handover note [hbase-agents/H1-H5.md](hbase-agents/) (copies of `/bigtemp/vnr3ne/analysis/hbase-2026-10-19/handover/H1-H5.md`) (exact run dirs, snapshots,
tree sets, launch commands). Nothing runs on any lift.

**1. The next runs, in this order** (OPERATIONS §10: a snapshot of `system/hbase`'s head, a tree set of
`gc/hbase-checks` 985a0dfe91 built with its own Maven repository, image vm-force12, workers every host the head reaches
in batch ssh -- lift15 failed that from lift03 (HP10-14) --, heads on hosts of their own; `tools/analysis/vacuity.py` on
every UNSAT before its STATUS row; a reading in `analysis/hbase-2026-10-19/readings.md`):
- **hbase-adhoc-04 = HBASE-30484**: DONE, PASS (NR3-04, 2026-10-20: SAT confirmed, reproduced 7/10, control 0/10;
  HBASE.md §E).
- **hbase-bugs-master-active-time (#11)**: rerun on `system/hbase` (>= 208ac1899: unplaced clocks placed). Offline
  its claim 0 is CLOCK_SKEW, T0 = T1 + 60001 ms; CONFIRM must plant T0 on master0's clock at its activation reading
  (`HMaster#finishActiveMasterInitialization`, `EnvironmentEdgeManager#currentTime`) and deliver it as the
  OpenRegionRequest's `initiating_master_active_time`; master1's `throwOnOldMaster` then throws. Item 2 has the gaps.
- **hbase-bugs-ns-rsgroup-removal (#13)**: run on tree 985a0dfe91 (tree set `/bigtemp/vnr3ne/wt/hb-checks-trees-20`,
  built, its 6 workloads native-PASS; launch command in H4.md). Expected chain: an `HBASE_RPC` REQUEST fault on the
  master's hbase:meta Mutate in `CREATE_NAMESPACE_INSERT_INTO_NS_TABLE` (one attempt in automatic mode) ->
  `addOrUpdateNamespace` throws before `cached()` -> `removeRSGroup` reads `namespacesInGroup == 0` and removes the group
  -> the held retry inserts the namespace -> CreateTableProcedure's `checkGroupExists` #3 reads null -> :227. Risk:
  PLAN may not admit that Mutate door as a control producer; then check the count's writer is in the closure.
- **hbase-adhoc-22 = HBASE-30483**: rerun with the full budget (COMPOSE alone > 10 min). The right claim exists (HC13);
  if "run published no target row at anchor ..." recurs, read CONFIRM's replay at that anchor
  (`accept-HC13-22/.../final/refuted/000*`).
- Then 10, 11, 12 (on >= 8da6eb24d: CallQueueTooBigException cut, fault replays queued last), 31 (new workload,
  selector `REGION.4a0683a9...#1`), 15 (tree set 9; read the NOT_ADMITTED first), 24 (seed replay once the chores are
  off), 21 (workaround 23ff06c9ba), 08, 14, 35, 28, 07, 19, 20 (19 and 20: a SEED-only run first,
  `STOP_AFTER=SEED`, to check the occurrence).

**2. master-active-time's CONFIRM: two engine challenges** (H2, HZ13-mat; both stand behind workarounds or partial fixes):

HZ13-mat, 2026-10-19), each standing behind a workaround or open:
- A clock planted in a retried occurrence is exported with no root mint row. `RootMint` planted
  `OpenRegionRequest.MasterSystemTime`'s reading (`DefaultEnvironmentEdge#currentTime`) as a symbolic `Long` box in
  the dispatch region's retried occurrences (`TimeoutExecutorThread#run#u27` -> `ExecuteProceduresRemoteCall#run`, a
  forced RPC fault's retry), the export cites it (session `1d963972f9596c7c-d98683ce`: expressions node 3301, export
  seq 2650), but the session's roots name no such symbol, so COMPOSE refused every arm resting on it as
  `UNSTATED_VALUE` and the seed path with them. Workaround: STATUS "tree: master-active-time's dispatch export" (no
  master system time in automatic mode). The fix publishes a planted clock's mint row wherever its box is exported.
- CONFIRM compares a WIRE leaf a clock carries with the text the model's session recorded (refuted HZ13-mat 0000 and
  0002: `2efac300f9e6d4d6` model "1792454828365", run "1792455517516"), while the replay's clocks are not the
  recording's. Open: such a leaf should be held to the model's clock value (planted) or compared by its expression.

**3. An order no hold realizes is checked, not refused (built 2026-10-20, H3; 04 reproduced with it, NR3-04 7/10).** HC21-04's
REPRODUCE planted nothing ("ORDER_UNHELD" on client0's `FutureUtils#addListener` continuation in
`AsyncMasterRequestRpcRetryingCaller#doCall`). The chosen read (the flush's `TableStateManager` table-state map at
the DisableTableProcedure step's DISABLED write) orders every other writer before that step; the step is a hand-off
task that serves the procedure scheduler, so its hold walks to its anchor's producer, the test's DisableTable
request, which is sent inside a continuation (claimed, no producer); and the same procedure's DISABLING step stands
under that request's anchor, so a hold there would have waited on its own effect. CONFIRM had no such hold either:
HC21 confirmed only because its selected session was itself the run. Now such an order is checked at its later
end's own activation (`check: true`, PIPELINE §10/§10b): observed in order or a mismatch, never waited for.
Open: a hold at a send whose earlier end depends on that send through work no anchor chain names (a continuation
registered by its reply) still waits until the order's timeout.

**4. A free `unsupported__` leaf in the seed's own fatal** (15): fixed on `hbase-reask` (TODO "Solr: after SGF9" §5,
PIPELINE §8): offline on HP8-15's corpus the claim is STATE_PAIRING_FLIPPED on path 62 (RegionStateNode.state re-paired
to OPENING plus one FAULT marker) instead of FORMULA_SAT on the seed; H1 reruns 15.

**5. Unmerged work.** `hbase-reask` 231264aad (WIP, not gated: item 4). Everything else of H1-H5 is in `system/hbase`.

**6. hbase-adhoc-34: done** (NZ3-34 PASS, 2026-10-20). Left open from it: a provenance site on a container field (`allKeys` in `retrievePassword`) still reads its receiver, the manager no decode registered; the fetch was asked through a declared read's receiver (f6e07b3c9). A guard that reads only a container's value, with no field read of the decoded value in its occurrence, would still cross to no fetch: then a container provenance site should take the versions of the values it returns (`Provenance#observe`, `RuntimeSelectedRegionFinalizer#askFetches`).

**7. hbase-adhoc-10's cost.** R17-10: 244 of 281 NOT_ADMITTED are one `FlipQuery#build` refusal ("this query declares no
variable of its own, and its occurrence read values no row of the corpus wrote") at 29 procedure-framework sites. Measured
(H5, 2026-10-20, each obligation dir's host.txt to its result): 459 s of solver time in all (median 1.5 s, at most 36 s),
answered on the hosts' served solvers beside other questions, no replay -- against 111,500 s of ADMITTED replays (36,
median 3,957 s) and 8,995 s of NOT_ADMITTED ones. Refusing them in PLAN would put a query build per candidate on the
planner's serial path to save parallel seconds: not done. The cost was 210 REQUEST-fault replays (~10 min each), now 140 behind the guard's own flips (8da6eb24d). If 10 still
does not converge, measure which client calls' faults reach the guard's cone at all before asking them.
Since H5's DUPLICATE_WORLD (PIPELINE §7.3): the repetition behind NR1STOP-10's growth -- the anchor path's two re-runs
in the seed's world re-ran all 70 client doors and each door fault was asked again from each re-run's path, 279 of the
315 fault replays queued at the stop repeating a world already replayed -- is gone; rerun 10 on it.


**8. A continuation chain re-registered per poll stands under the poll count.** A continuation now stands at its
registrant's address wherever it runs (IDENTITY §6, `runtime/Continuations`; hbase-adhoc-11 and 12's `Admin#move`).
A chain that re-registers itself per poll (a procedure's `getProcedureResult`, rescheduled on the HashedWheelTimer
until the procedure is done) nests one start frame per poll, so the request after it stands under the poll count k,
which is timing (hbase-adhoc-21 HC11-21: `MasterService.RestoreSnapshot` planned under `7be160aff4b342f7`, ran under
`b6701a92041c9536`). Until a poll stops counting (a claim of the same start site under itself restarting at its own
frame), such a workload makes the operation its own synchronous call on the test thread (hbase-adhoc-21's restore
without the failsafe snapshot). Also open from the review of hbase-rpc 7384c1e61 (`review-cont/REVIEW.txt`): the VM's
activation stack, store-read rows and wire exports do not stand apart in a continuation (M3: a marker on
`ConcolicRegionRuntime` like `SILENCED`, popped at the claim's end, then a case whose planned region registers a
listener); an unnamed registrant folds where it runs and files no gap (L3); a queue claim inside a continuation with no
woven frame between can drop the continuation's start frames (L4); `LineageScan` selects registrations by the exact
owner `CompletableFuture`/`CompletionStage`, the weave by hierarchy (L5a); Netty and Guava future listeners and static
`supplyAsync`/`runAsync` are no continuations (L5b); a poll chain's index grows by one frame per poll (L6).


**9. Data through a region's store and chores as race partners** (13). `hasMergeRegions` reads the hbase:meta row's
cells, which reach the master through the meta region's memstore and a Get reply: no tracked cell carries them and
`Result`'s map is sorted (`ordered_map_unmodeled`), so the guard is concrete (HP9-13: 14/14 fatal arms literal false).
Its race partner, CatalogJanitor's GC of merged parents, is a chore that never comes due in automatic mode (tree
f9340f2aab). Reaching 13 needs a model of a Put -> store -> Get (a STORE door keyed by row/family/qualifier, as
ZooKeeper's store is keyed by path) and a workload that drives the janitor, as 04 drives the quota observer.


**10. A znode's absence as state: tombstone lives + a store-read pairing flip** (H2 design, lead 2026-10-19: not
built until a case's chain needs a read in an absent window; it serves Solr and HBase alike). Today neither system
states absence: a delete takes only its parent's WRITE turn, a NoNode `getData` throws before the read hook, an
`exists` of no node is a trace row only (`MessageDoors#read` returns for version < 0), and a re-create starts a new
location life (`path#k`). (a) One location per path with (life, version) states: a create opens life k, a delete
(a multi's delete op too) and every ephemeral of a closed or expired session (the expirer and the client's close ask
the in-process server for the session's ephemerals) file a TOMBSTONE write ending it, a NoNode read is a STORE_READ
of that tombstone (before any create: INITIAL absent), and a read's eligible writers are the path's creates, sets,
deletes and expiries across lives; table tests in `MessageDoors`/`RecordedStore`, a Solr regression check (~half a
day). Alone it moves nothing: a store read is held at the version its session read (CONFIRM's STATE row), so it only
makes deleters writers in the chain and an absent read a held row. (b) A store-read pairing flip, `PairingFlip`
generalized from VIEW reads to plain store reads: the replay holds the reader's READ turn until the asked version's
WRITE turn (a tombstone) and before the next life's create, CONFIRM refutes it as `PAIRING_UNTAKEN` as for views
(`ScheduleLog` turn holds, `Confirmation`, `FocusedReplay`: large). It would let a check like hbase-adhoc-37
(`MasterAddressTracker:206`, `data == null`) be asked in a failover workload; 37's own workload has no absent window.

**11. Smaller HBase items.**
- Two region servers' ZooKeeper event threads ran under `workload/unregistered ... Lost:UNKNOWN` in hbase-adhoc-24's NZ3-24
  (LINEAGE_LOST 56 named rows; their getData rows stand on no node): a ZooKeeper event thread of a server started before
  its registration is no node's; check `CausynthNodes` registration of `ZKWatcher` event threads if a case needs them.
- A procedure step that only met a busy entity lock (`LOCK_EVENT_WAIT`) or yielded is a step too, so where two
  procedures contend the later steps' occurrences can be renumbered between runs; if a case shows it, hand the next step
  off from the empty step's own hand-off context. Shown natively by hbase-adhoc-04 (owner ruling: 7/10 is a PASS, not
  pursued): in repro-NR4-04 the DisableTableProcedure's DISABLED step (activation `4fb72968fe9e4893`) never ran under
  its confirmed identity in 2 of 10 runs and createTable's ENABLED step (`3072f5195129abb3`) in 3, where
  `ProcedureFutureUtil#suspendIfNecessary` suspended a step in one run and not in the other, so the next hand-off nests
  one level deeper or shallower (NR3-04: 3 of 10).
- A refuted message re-pairing is re-found on every other path, ~10-15 min of COMPOSE+CONFIRM each (hbase-adhoc-31
  NR8-31: 9 claims, all rs3's executeProcedures consumer re-paired to another session's message, until
  campaign_max_claims). A sound cross-path exclusion needs a refutation reason that does not depend on the path's world
  (the same consumer/producer pair may be feasible where the old incarnation's request is really resent); the same
  family as master-active-time's cross-session constant arms.
- StaleRuns (COMPOSE frees a value a stale run left concrete) was built and reverted (655b88023): on HZ7-mat it changed
  nothing; rebuild only when a claim's path takes a value through a read whose writer ran paused and runs whole now.
- Identity of threads libraries start (ZooKeeper's EventThread, Netty loops): per-node Netty groups and timer lineage
  cover HBase today; a message exported on one thread and sent by another after a queue is settled (IDENTITY §7.1).
- `hbase-reask`'s offline tools (`analysis/hbase-2026-10-19/reask/`: compose-run.sh, plan-run.sh, case-evidence.sh,
  probes) re-run COMPOSE/PLAN on a run's inputs; `SmtLowering.forSession`'s repair predicate differs from the
  Composer's, so a probe through it is not the Composer's answer.
- Housekeeping: old snapshots (`/u/vnr3ne/gc-run/hb-*`) and tree sets (`/bigtemp/vnr3ne/wt/hb-*-trees-*`) listed in
  H1-H4.md (e) can go once nothing reads them; `system/hbase` is not pushed to GitHub (owner's OK needed); the fork's
  `graphchecker/hbase-checks` is pushed at 985a0dfe91.

**12. Provenance through a construction-only container field of a copy-on-write object** (hbase-bugs-ns-rsgroup-removal
NC3-nsrg, worked around in the tree 100878f553, STATUS "the H4 checks' stated guards"). `RSGroupInfoManagerImpl#getRSGroup`
read `holder.groupName2Group.get(name)`: the guard's term names the MAP read of the holder's map, whose only static writer
is `RSGroupInfoHolder`'s constructor storing into its own object (`ownObject`: only the guards choosing which
construction runs, `flushConfig(Map)#u3`, SYMBOL-SCOPE §3), while the REFERENCE read of `holder` naming WHICH holder (and
so which map) is in no term, so the store that hands the new holder on (`flushConfig(Map)#u30 holder = new ...`, guarded by
`removeRSGroup#u52`, the namespace check) never offers its occurrences: the removal's static-candidate demand had flip
sites `[flushConfig(Map)#u3]` only (offline planner over NC3's corpus), `#u52` was never a flip site in 127 rounds (NC1),
the count read was never demanded and neither the namespace Mutate fault nor the race was asked. The general fix: a
demanded read of a container reached through a construction-only field also demands the read of the reference that
handed its owner on (`Provenance`, PROVENANCE sites), so the handing-on store's writers and guards join the closure.

**13. A continuation's registration as its submitter (designed, parked: no current case needs it).** An order whose
work's submitter chain (`Confirmation#submitter`) ends at a continuation claim names no send, so it is checked, never
held (every master admin call is sent inside `AsyncMasterRequestRpcRetryingCaller#doCall`'s `FutureUtils#addListener`
continuation). Design (H5, 2026-10-20): `Identity#startWork`, for a continuation carrier and when ordering, calls
`Confirmation.entering` on the registration (the Start key the rows carry as `ActivationRow#threadKey` after `start:`,
its context normalized as activations are), before the registering call, so the listener runs after the hold whether
it would run inline or late; `ConfirmMain.StateClosure#held` holds there instead of checking, except where the
registrant is an event loop or a reply leg, or the earlier end's own chain reaches a later registration of the same
registrant (program order: the held thread would wait on work it has not issued) -- those stay checked. Measured
(offline ConfirmMain plans of every refuted claim, `analysis/hbase-2026-10-20/reask/confirm/*.probe`): NC2-22's 30
orders are all checked because of a client continuation, 22 match natural timing and 8 (one per claim: the deletion's
release after the creation's count read, the bug's counterfactual) contradict it, and those 8 fall under the
program-order exclusion (the test thread registers the delete, doCall@5, before the create, doCall@6), so the hold
would confirm nothing there; HC14/HC15-nsrg: 85 orders, all held where they run, all in natural order. 22's real
blocker is that its procedure steps are `servingTasks` (item 14).

**14. Procedure steps marked serving by their own continuations (fixed on `hbase-reask`, not yet rerun).** Since tree
1dda23ecc5 (steps are `HANDOFF_TASK`s) and engine 28ec6763b (a continuation's claim is never run-here, so always
consumed), every step's own hbase:meta write -- `AsyncSingleRequestRpcRetryingCaller#doCall:108` /
`AsyncRegionLocator#getRegionLocation:158` -> `FutureUtils#addListener:64` on a done future, its listener run inline on
the PEWorker -- made `State#openStart` mark the step serving (NE3-22's seed replay, a debug snapshot of 8b4ae7a9f: all 5
claim kinds that marked a step were same-thread continuations; no item claim did), so every ORDER on a step went to the
client's send or was checked. Now only work another thread started (or an unknown or ended starter) marks a hand-off
serving. Offline on NC5-22 `refuted/0000` with its session's step starts dropped from `servingTasks` as the rule now
drops them (`analysis/hbase-2026-10-20/reask/confirm/nc5-22-0000-{orig,sim}`): its 3 ORDER rows go from check:true
(through the client continuation) to held where they run, the deletion's release at the DeleteTableProcedure step.
Seeds with step starts in `servingTasks` before the fix: 22 (27), 10 (48), 14 (54), 04 (12), mat (12), nsrg (3-4), 35
(4), 28 (3), 34 (3); 04 keeps its PASS (confirmed under the old rule; the change only adds holds). A step so held is
held at its claim's entry (`Confirmation#claim`, before `acquireLock` and `beforeExec`; PIPELINE §10 has the argument),
since a TRSP step held at the last activation before its write would sit on its RegionStateNode lock, which the admin
move/unassign's `preTransitCheck` (10/11/12's targets) and region state reports also take, and as NC9-22's release was
held inside `synchronized NamespaceStateManager#removeTable` (the creation blocked on that monitor, 300 s timeout) --
except where the earlier end runs inside the held claim (its `threadKey` the claim's or extending it: H3's review) or the
claim finishes another order's earlier end before the event (a cycle of entry holds: NC9-22's final claim), held before
its event. NC10-22 (hb-int-5) is the first live run of the entry hold. First runs on the fix: check
`servingTasks` holds no step start and that no ORDER on a step times out.

**15. COMPOSE orders a client thread's synchronous call past its own later event** (hbase-bugs-ns-rsgroup-removal
NC7-nsrg, `gc-out/hbase-checks/accept-NC7-nsrgSTOP-claimloop/.../schedule/witness-confirm/000*` and `final/refuted/000*`;
measured 2026-10-20, H5). Its final claims 0 and 1 join the CreateTable step's group read (`acbbc512`, under request
`d339f15a`) to INITIAL of the rsgroup map, or to the startup worker's flushConfig (v18/v50), past the writes of the test
thread's earlier synchronous calls: v200/v202 in AddRSGroup's handler turn (claimKind NONE, `Anchor:dca8879d`) and
v473/v475 and v776/v778 in MoveServers' handler turns, all of them under the test stance `Root:CLIENT/test#1`, whose
reply RECV rows (401/533/871) come before R2's SEND (1023). The 4 witness attempts have the same shape. CONFIRM refutes each
one after the 300 s order timeout, and composing them cost 704 s and 317 s (36899 and 42922 z3 runs). hbase-adhoc-22 NC11 is
NOT this case (no truncate write exists; its claims skip only DeleteTableProcedure's release, claimed work), and neither is
#11 NZ2-mat (INITIAL of master1's own activation write, and the cross-session constants).
Facts that hold in every world executing both events: F1, program order inside one activation; F2, SEND(e) before the
turn `Anchor(e)`; F3, a handler turn's own (claimKind NONE) events before its RESPONSE SEND, before that reply's RECV on
the sender. F4, "the client waited for R1's reply before it sent R2", is NOT in the records: nothing records a thread
returning from `FutureUtils#get`, and `contract.ClientProgramOrder#repliedBefore` (H4, REPRODUCE) reads the recorded
order, which an asynchronous call whose reply came early also shows. The completion poll (a procedure step reaches the
client only through the poll handler's read of the procedure state) is left out. Rule (b): a write W2 between the
alternative writer and the observed one, with W2 in a NONE turn directly under client request R1, X under client request
R2 of the same stance, and F4(R1, R2), is not concurrent with X (`Arms#eligible`'s check of the writes between), so the
earlier writer is not eligible. Built offline with `repliedBefore` as F4 (not merged, lead 2026-10-20: a completeness risk
to no open case's benefit): NC7's corpus composes the fault claim first (MARKER_FLIPPED on `REGION.ac7e6e0e..in.26120816`,
NC12's confirmed root) in 114 s with 798 z3 runs. The sound F4 needs new records (design below). PARKED (lead,
2026-10-20): 2-3 days of identity/schedule work for two study cases whose results already stand as named bounds (hbase-adhoc-08
NC14-08 and hbase-adhoc-14: every claim up to `campaign_max_claims` refuted by the client's program order) fails the owner's
workaround-over-grinding rule. Build it when a case's verdict depends on it. Cases it bounds now (each a named bound `campaign_max_claims`, every claim refuted by CONFIRM after a full replay, about 8-10 min a claim for CONFIRM plus 2-12 min for its COMPOSE): hbase-adhoc-08 NC14-08 (9 claims, 6507 s), hbase-adhoc-14 (the merge's `encodedRegionsMap` read before CreateTable's put, NP10-14), hbase-adhoc-15 NP9-15 (9 claims, CONFIRM 475-531 s each, COMPOSE 154-730 s each, 11381 s: the merge before CreateTable's steps and the OPENED reports), hbase-bugs-ns-rsgroup-removal NC7 (its program-order claims; NC12's fault claim confirmed).
- The chains it must state. nsrg runs: R1's handler turn, then its RESPONSE, then the reply reader (`Anchor:r1`, netty),
  where `RawAsyncHBaseAdmin`'s `RpcCallback` completes the RPC future G. Then `AsyncMasterRequestRpcRetryingCaller`'s
  `whenComplete` continuation C, registered on G, completes the caller's future F, and the test thread's
  `FutureUtils#get(F)` returns. The test thread then registers `doCall@k+1`, which sends R2, under which the read X runs.
  14's merge is an in-JVM submit after the synchronous createTable returned: a START, not a SEND, so the fact must order
  the waiter's later events, not only its sends.
  Every hop "a future completed, so its continuation ran" is itself a completion edge. A row that names only F's completer
  does not reach R1.
- Records. Positions are VM event ids, the space of the rows' `seq` and the schedule's `vmEvent`.
  (a) COMPLETE, in memory only: woven before `CompletableFuture#complete` / `#completeExceptionally` (when the future is
  not done), and at the end of a carried continuation's claim for the dependent future its registration returned. It maps
  the future (`RuntimeObjectIdentity`) to its completer {occurrence, activation or claim key, event id}. A `thenCompose`
  dependent, or a completion in code that is not woven, has none: no fact (sound, no gain).
  (b) A schedule row `JOIN`, woven after `Future#get()`, `#get(long, TimeUnit)` or `CompletableFuture#join()` returns:
  {waiter context, occurrence, event id; after = the future's completer}. For HBase every synchronous Admin and Table call
  goes through the woven `FutureUtils#get`.
  (c) CLAIM rows gain `after`. For a continuation it holds the completer of the future it was registered on
  (`CausynthPipeline#carryContinuations` passes the call's receiver). For any claim it holds its registration point
  {registrant occurrence, event id}, because continuation registrations write no START row today.
  `LineageScan` keeps every class with a `complete*`, `get` or `join` call (`AsyncMasterRequestRpcRetryingCaller`, which
  completes the caller's future, is not woven today).
  JOIN is observation-only: it is written without `admit` or holds, and `SchedulePrefix`, `ScheduleLog`'s order load and
  REPRODUCE skip it. The new CLAIM field is ignored by enforcement.
- One helper, contract `HappensBefore`, built from a session's schedule, activations and rows, absorbs
  `ClientProgramOrder`. Its nodes are (occurrence, event id). Its edges: program order inside one activation; F2, SEND(e)
  to the turn `Anchor(e)`; F3, a NONE handler turn's events to its RESPONSE and then to the reply reader; completer to
  CLAIM `after` and to JOIN; registration to claim. hb(W2, X) holds when W2 reaches X's past. `Arms#eligible`'s check of
  the writes between and `ConfirmMain#implied` (REPRODUCE, H4) both read it.
- Cost and proof. One JOIN per blocking get in woven code, about the number of synchronous client calls: 22 about 75 (of
  4319 schedule rows), nsrg about 21 (of 867), 10 about 76 (of 32743), under 2 %. Estimate: 2-3 days of code (contract
  kind, field and codec; weave; runtime; HappensBefore; Arms and ConfirmMain; prefix, order-load and plant exclusion;
  tests; docs), H3's review (identity and schedule). Then SEED-only runs of 08 and 14 to show the JOIN and CLAIM `after`
  rows, and a fresh SEED and EXPLORE of nsrg, since only new recordings carry them. Then re-COMPOSE offline on the three
  corpora: their refuted program-order models gone, NC12's fault claim kept.

**16. A large start starves on a busy pool (platform/ledger; H1, not built: no bug case blocked by it yet).** A stream start
(`campaign_stream_admit_host`) that no host admits only logs "waiting for room" and retries; nothing reserves room for
it, so while the shared pool is busy every smaller start of every run is admitted ahead of it, and a large one may never
fit. Measured on hbase-adhoc-15 NP6-15 (`gc-out/hbase-platform/accept-NP6STOP-15-starved`, hb-int-2, five agents'
runs on lift02-15): from about 02:28 to its stop at 03:00 (2026-10-20) it sat at EXPLORE round 175 (wave 10) with 133
obligations and 0 in flight, each obligation solve charged 7917 MB after "its host's solver ended for memory before it
answered; asked again of a host's solver" (the re-ask at twice its slot); every host refused it (e.g. lift10 26496 MB
charged / 12156 MB in use, lift04 19584 MB charged + 15488 MB held for a head, against the 22109 MB limit, 70 % of
31583 MB) while smaller replays of the other runs kept being admitted. The precedent is the head step's hold
(`campaign_head_hold_room`: a waiting head step writes its need as a `heads/*.hold` on the host with the most room,
which `campaign_host_head_room` subtracts from every other start there, so that host drains until the step fits; the
hold goes when it is placed). Extend it to stream starts: a start that waited longer than a bound (minutes), or whose
need exceeds what any host admits beside the charges standing, holds its need the same way on the host with the most
room (one hold per run at a time, the largest waiting need), released when it is placed or the run ends.

**17. COMPOSE has no happens-before through a volatile publication; a refuted INITIAL pairing returns per path and
session** (hbase-bugs-master-active-time, NZ2-mat 2026-10-20). `MasterRpcServices#reportRegionStateTransition` calls
`checkServiceStarted` (volatile `HMaster.serviceStarted`, written in `startServiceThreads` after
`finishActiveMasterInitialization` wrote `masterActiveTime`) before `throwOnOldMaster` reads `masterActiveTime`, so no run
reads that field's INITIAL value there. COMPOSE offered the INITIAL re-pairing anyway: it made the recorded valuation
satisfiable (polarity undecided, so the CLOCK_SKEW claim was never named) and every path or session variant of the
same pairing became its own FORMULA_SAT claim (claims 0 and 1: `writer_arm` INITIAL|INSTANCE/<obj>#664, refused in the
replay by `ServerNotRunningYetException` and by ORDER `ad500b7c5e0bdd13`), ~25 min each (DECIDE 1191 s over a 187 MB
formula, 424 paths), because the claim loop excludes only the selected path's arms. Worked around in the tree (STATUS
"tree: master-active-time's served active time"). The engine fix: a read that follows, on its thread, a read of a
volatile that saw write W excludes every version its location had before the last write that precedes W on W's thread
(the JMM's synchronizes-with); or exclude a refuted pairing by its reader site and slot across paths. Also from NZ2-mat
(H5's probe, `analysis/hbase-2026-10-20/reask/probe-mat/`): 301 message arms bound the hand-off leaf (the initiating
active time) to other sessions' recorded constants, 15 of 16 above the seed's T1 because those sessions ran up to an hour
later in wall time -- worked around by a run-relative clock (STATUS "tree: run-relative clock"); the general fix is a
leaf a clock carries taking its producer session's clock value relative to that session's own timeline.

## ZooKeeper (`system/zookeeper` = main today)

**1. Merge `hb-schedule` + `hb-sync`** onto the new body. Run the offline gate on V25; live runs of quota-init,
election-offer and 11741, comparing arm counts and refutations with V25. The ZooKeeper tree with the RESPONSE door is
`gc/zk-unified-hb` `47ddc8b36`.

**2. A quorum adapter.** Every selected ZooKeeper study test is a quorum test. Register each quorum peer as a node;
open the window once the quorum is up.

**3. Mark the 10 checked points** (`docs/checks/ZOOKEEPER.md`):

```
01 02 03 04 06 07 10 11 12 13
```

05 is a dead throw; 08 and 09 have no path.

**4. zk-bugs-container-reuse (#33).** A self-written ClientBase test; STATE re-pairing of the client's node-map lookup
to the cleanup's delete, the election-offer mechanism.

**5. Run the group of 13.**

## Cross-cutting (engine), when a system needs it

**Force the fatal arm inside the target region (owner 2026-10-08; from the next system on, HDFS stays as closed).** The
owner: "事实上我觉得这里我们就可以直接针对这个region强制反转，记录条件然后throw出exception啊。即使他不符合真的因果。但我们会结合
symbolic propagation联立的。请你把它设为todo"; "这样绝对是doable的。我们完全可以做到强制反转，你可以通过soot,vm等结合实现。然后在那个
target region里记录下path conditon即可。就可以之后直接用了". Built on branch `solr-force-arm` (PIPELINE §7.10; design
`/bigtemp/vnr3ne/analysis/solr-2026-10-08/design-force-fatal-arm.md`, the lead's rulings: always run the FORCE replay, no
transplant onto other paths, nested flips kept, no flip waiting for the forced ones): SEED's forcing table, the VM's forcing native (image
`vm-force1`), the FORCE run first in every campaign, its forced session held apart, its forced flip asking the whole way to
the throw, its path one more COMPOSE disjunct, CONFIRM unforced; solr-18413 and solr-18406 PASS with it (FA4). Merged on
`system/solr` (fa70dae08, image vm-force4+). A loop bound counts only iterations that decided on a symbol (the CREATE-a-core
checks' FORCE runs were cut by a concrete loop), a branch both of whose arms reach the throw is never forced, and a path
stopped on the way is BOUNDED (`solr-force2`, PIPELINE §5, §8). `seedFlipsAfterForcedFlip` was 0 in every Solr run of
agent F2 (so the seed path's anchor flips and open-arm asks may be deletable: decide on SG3's numbers). Waiting on Z2:
solr-adhoc-19's forced flip (its phi reads `clusterProperties`, parsed from ZooKeeper JSON).

**A transient ZooKeeper fault inside the retries (lead 2026-10-13, for later).** Every Solr ZooKeeper door stands at
`ZkCmdExecutor#retryOperation`'s boundary (SYMBOL-SCOPE §4.2): a planted ConnectionLoss escapes past the retries. The
transient world -- one ConnectionLoss inside the retries, retried, the retry meeting `NodeExists` (a create the first
attempt applied) or a duplicate sequential node -- is planted nowhere since makePath's hooks left its retry lambda
(`makepath-create-tree.patch`). A general in-retry door: the system names its retry wrapper (a doors.jsonl row), and a
door inside the wrapper's operation plants a fault on one attempt only, the wrapper retrying as it would.

**WIRE-CODEC (`wire-codec-p1`; the system body carries none of it).** Resume only when a system's chain needs a
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
(Solr §2) beside the ZooKeeper READ doors.

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
