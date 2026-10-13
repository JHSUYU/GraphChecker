# TODO: HDFS finished, Solr in progress (handover 2026-10-12)

Order:
1. HDFS is finished (STATE §0): its follow-up items below are optional engine work, done when a later system needs
   them or before a clean final acceptance run.
2. Solr: in progress, stopped by the owner for a handover on 2026-10-12 (section "Solr": what is merged, the
   three branches in flight in merge order, the ZooKeeper READ doors, the open problems, SG3 and the fork).
3. HBase.
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
- **A host solver answers one question at a time** at 12-14 GB resident on 07's corpus: more answers per solver JVM
  (or a smaller one) would lift the solve throughput and the memory every lift gives replays.
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

## Solr (in progress: the final round SGF from `system/solr`; worktree `/bigtemp/vnr3ne/wt/gc-solr`; lead session 2026-10-12/13)

**Read first:** STATE.md §S, then this section, then STATUS "Solr checks" and the lead's notes and readings in
`/bigtemp/vnr3ne/analysis/solr-2026-10-12/` (readings/ per case; the earlier stop's are in `.../solr-2026-10-11/`).

**Goal** (owner 2026-10-08, restated 2026-10-11 /goal): the 20 Solr cases each get an `.smt` whose causal chain is right.
- The 8 bug checks end `SAT_CANDIDATE`: the witness confirmed by a CONFIRM replay, reproduced natively (>= 1/10), and the
  `.smt`'s chain is the bug's chain (read against 8.11.4, CHECKING.md).
- The 12 study checks (05 07 09 10 13 14 19 21 31 38 39 40): a SAT is confirmed, an UNSAT stands at its true fixed point or
  at a declared, named bound where the closure is genuinely too large (owner 2026-10-12, RULES). A study SAT that passes validation is a new-bug candidate: realism, JIRA, STATUS.
- Every `.smt` is read by hand (CHECKING §2) and its row written in STATUS "Solr checks".
- solr-18406, solr-18413, migrate-buffer-leak never regress; the end is one round of all 20 with no regression.
- FP rule (owner): a CONFIRM replay that does not reach the exception, times out or stalls is a false positive, excluded,
  next claim, up to 8; then "every SAT filtered as FP" (not RUN_DEFECT). Every `restsOnRefutations` entry read. No real
  witness of the 8 bug checks may be filtered.
- One Solr tree pushed to the fork `https://github.com/JHSUYU/solr.git` branch `graphchecker/solr-checks` (never
  apache; `~/lucene-solr-8_11` is unshallowed); trees.tsv, prepare-trees.sh, solr-cases.tsv, REPRODUCE §6; verified
  from a fresh clone. Pushing the fork is pre-authorized by the owner's goal; any other push needs the owner.
- Owner rulings of this session (RULES.md): refactor only when truly necessary; identity keeps semantic counts only
  (memory feedback-identity-semantic-counts); only Solr (no HBase work).

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

Image: `/bigtemp/vnr3ne/vm-force5/j2sdk-image`. Canaries on the merged body: IB2 (301871532) 18406/18413/migrate PASS
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
- `solr-solve`: the solve's two lanes, a busy solver's question withdrawn after 30 s; host solvers start at 2 GB and
  double on exit 3; one-question and retry JVMs charged their footprint.
- `solr-str`: String.toLowerCase/toUpperCase lowered exactly over ASCII.
- `solr-str2`: every String arity the VM emits with an exact SMT-LIB form z3 decides: `startsWith(p, off)` (39's
  59 refused paths), `indexOf`/`lastIndexOf` with a from index and code points, `regionMatches`, `compareTo`,
  `subSequence`, `equalsIgnoreCase` with a literal side; the rest refused by name (VM.md, String row).
- Lead: an engine JVM is charged its footprint H + H/16 + 384 MB; a stream replay its typical peak (p90 x 1.25 after
  eight); `launch-round.sh` passes CASE_TIMEOUT_SECONDS, PRUNE and CAUSYNTH_CAMPAIGN_STOP_AFTER to the heads.

### 1. Branches in flight

None of GraphChecker's: every `solr-*` branch is merged or superseded. Solr tree work: agent SC's Overseer batching-wait
workaround for 31/05's seed drift (a branch from gc/solr-final5; folded into a final6 by ST only if it halves the seed
give-ups, else dropped with the earlier idle-wait hunks, §3h).

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
  flip is an OperationTimeout (a single ConnectionLoss is retried and meets NodeExists). Analysis
  `/bigtemp/vnr3ne/analysis/solr-2026-10-12/readings/lock-leak-SG3I.md`; pre-reading `.../solr-2026-10-11/readings/lock-leak.md`.
- **b. 18413:** both SG3G/SG3H refutations fixed (§0, Z2); CONFIRM watch: a seed arm with a Lost-context consumer and arms
  whose sites carry queue sequence names (qn-...) can shift identity between runs.
- **c. Seed drift of 31 and 05:** give-ups at the Overseer's `peekElements` WAKE turns (k counts every wake, a timing
  count). SC's experiment (2026-10-13, int11): `gc/solr-sc3` f10c988eed = `gc/solr-final5` + the batching wait 0 in an
  automatic cluster (`Overseer$ClusterStateUpdater#run`'s `peekElements(1000, 100, ...)` after a message; final4/final5
  already carry the idle wait that never times out, which alone moved nothing: 05 158 -> 163, 31 18 -> 23 give-ups by the
  same slots). With both, 05's recorded wake turns 51 -> 39 and its seed ended at 47 give-ups (SC12-05), against 158-163
  by the same slot (~2,200 of ~4,800; SC8-05, SC10-05). 31 is not helped: recorded wake turns 52 -> 15, yet 19 give-ups by
  slot 327 as before (signal wakes, still counted by k), then 64 by slot 527 on its test client's polling reads (`READ
  /clusterstate.json#100, #101 ... @ client0`, 16 s each; SC12-31). Not in the final tree (lead 2026-10-13): SGF runs on
  one tree, final5; the patch changes the Overseer loop every bug check goes through; 05 already closed on final5-era trees
  with more give-ups (SF3 UNSAT_CLOSED in 3991 s). Kept as `gc/solr-sc3` f10c988eed for a revisit if SGF-05's seed fails
  or blows its budget on drift. Otherwise the frontier-side rule, not approved. Evidence `/bigtemp/vnr3ne/gc-out/solr-sc`
  (accept-SC8-05, SC10-05, SC12-05, SC7-31, SC10-31, SC12-31).
- **d. New-bug candidates:** 38 (SAT confirmed, native 0/10 named: native order beyond the fatal cone); the lost watch
  (§2); 19's stale cluster-property view at core creation if SGF confirms it. Each: realism, JIRA, STATUS,
  docs/checks/new-bugs.txt.
- **e. 14:** its forced phi is a constant (accepted); a ZooKeeper path's liveness and a server-side session-expiry root
  are not modelled (`.../solr-2026-10-12/readings/14.md`).
- **f. Producer-conjunct pruning in the flip query (after the group):** `FlipQuery#arm` asserts a handoff producer's whole
  path condition, so one guard's arm is another question in every upstream world (SC9-19 r13: 32 ids per arm, 7 or 1
  without the stated handoffs); keeping only the conjuncts sharing variables with the delivered term or the guard would
  make them one question -- a query design change, and what the depth bound stands in for.
- **g. Cleanup owed:** delete `MessageDoors#refreshing` (a no-op for trees before final4) and its external-callers row
  once no run reads an older tree; REPRODUCE's summary counts no VIEW_HOLD row (its jq reads ROOT/ANSWER/ORDER only).
- **h. Flaky test:** `ScheduleLogTest#aSettledConflictIsGivenUpOnceWhoeverAsks` failed once in a gate on a loaded lift09
  (2026-10-13, solr-int 13eca0d4c: 3 slots given up in 1 stall) and passed 3 of 3 alone: timing-sensitive.

### 4. The final round SGF and the fork

1. Snapshot `system/solr` (`tools/lib/worktree-add.sh ~/gc-run/sgf <sha> --detach`, build with `tools/onlift.sh`), trees
   `GC_TREES=/bigtemp/vnr3ne/wt/sg3e-trees` (gc/solr-final5). Launch each case with the lead's `launch.sh` (one head
   per case, obligations over every lift but lift11; budgets from `experiments/solr/solr-cases.tsv`), GC_OUT
   `/bigtemp/vnr3ne/gc-out/solr`, rounds `SGF-<case>`: the 8 bug checks first, the study checks as room frees
   (~8-10 campaigns live).
2. Verify each with `tools/rounds/round-verify.sh`; read every `.smt` with `tools/analysis/smt-legend.py --repo
   /bigtemp/vnr3ne/wt/lucene-solr-final5` against the readings and CHECKING §2; write each STATUS row; record every FP
   filtered ("COMPOSE SAT -> CONFIRM refute -> excluded -> UNSAT_CLOSED").
3. The fork: DONE 2026-10-13. `gc/solr-final5` 827b46a609 is `graphchecker/solr-checks` on
   `https://github.com/JHSUYU/solr.git` (apache untouched); trees.tsv, solr-cases.tsv and REPRODUCE §6 name it. Verified
   from a fresh clone (agent ST, report 27): a sparse clone of `system/solr` d119c91f8 built, `prepare-trees.sh` with the
   default SOLR_FORK cloned the branch, all 17 workloads PASSED natively and all 20 cases validate
   (`/bigtemp/vnr3ne/wt/fork-check-gc` + `fork-trees`, log `gc-out/solr-sg3/prepare-fork.log`). A later tree goes there
   as a fast-forward of the same branch.

### 5. Where things live

- Lead: memory `lead-session-2026-10-12-solr`; notes, readings, launch and watch scripts
  `/bigtemp/vnr3ne/analysis/solr-2026-10-12/`; the earlier stops' reports `.../solr-2026-10-11/HANDOVER-2026-10-12.md`,
  `.../solr-2026-10-08/HANDOVER-2026-10-09.md`.
- Rounds: the lead's `/bigtemp/vnr3ne/gc-out/solr` (LD*, SG3*, SGF-*); agents' `gc-out/solr-explore2` (RX*),
  `gc-out/solr-zk2` (Z2*), `gc-out/solr-sg3` (SP*), `gc-out/solr-solve` (SL*), `gc-out/solr-sc` (SC*).
- Snapshots: `~/gc-run/int1..int11` (solr-int stages; int11 = ce92cb6a6), `~/gc-run/sgf` (SGF).
- Trees (GC_TREES dirs, each a `lucene-solr-checks` link): `sg3e-trees` -> lucene-solr-final5 (the final tree),
  `sg3d-trees` -> final4, `sg3c-trees` -> final3, `sg3b-trees` -> final2. A case.sh `repo=` resolves under GC_TREES;
  the default `/bigtemp/vnr3ne/wt/lucene-solr-checks` is an old directory, never the one to run.

## HBase (`system/hbase` = main today)

**0.** Before any HBase run on the new body: `hbase-unified` `CausynthRpc.java:61-62` drops `, call.param` (the payload
door is gone with WIRE-CODEC); rebuild hbase-client.

**1. Settle `hbase-startup`'s two design questions** (the lead decides; see [STATE.md](STATE.md) §2):
- An identity rule for threads started by libraries (ZooKeeper's EventThread, Netty event loops). They must not
  inherit their racing creator's frames.
- Message-bound exports for a value exported on one thread and sent by another after a queue (what WIRE-CODEC's
  message-bound exports did; the body no longer carries WIRE-CODEC, so design it on the current WIRE path).

**2. HBase #14 (master-active-time) to a confirmed CLOCK witness.**

**3. Mark the 17 checked study points** (`docs/checks/HBASE.md`):

```
04r 07r 08 10 11 12 13 14 15 19 20 21 22 24 31 34 37
```

04 and 07 are re-sited to the server: `AbstractStateMachineTableProcedure.java:163` and `SnapshotManager.java:1046`.

**4. The two admitted bugs.** backup-lock-reply-lost: needs a RESPONSE door on HBase RPC (`checkAndMutate` with
NO_NONCE). ns-rsgroup-removal: STATE re-pairing of `removeRSGroup`'s namespace read.

**5. Run the group of 20.**

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

**WIRE-CODEC (`wire-codec-p1`; the system body carries none of it).** Resume only when a system's chain needs a
codec hole (a value carried inside an opaque payload); then rebase it onto the body, which deleted its runtime.

**VM performance.** The VM sends each expression node once per channel (STATUS open item 41). A plan budget should
be derived from the seed's measured cost.

**Timed-wait outcomes (owner 2026-10-09 discussion; the door is merged on system/solr 2026-10-11, the ORDER-row
model below is not built).** A guard decided by whether a timed wait
(`CountDownLatch#await(timeout)`, `waitForState`) timed out or was signalled is concrete today: the signal travels through
JDK synchronization the VM does not track (solr-adhoc-09: `DeleteReplicaCmd:278` needs both 30 s `waitForCoreNodeGone`
waits to time out). A general model: a timed wait's outcome is a schedule choice -- the signal before or after the
timeout -- that a flip may ask and CONFIRM holds by an ORDER row. Needed for the external study's DeleteReplica candidate
(Solr §2) beside the ZooKeeper READ doors.

**Decoded products' derived fields (agent Z2 2026-10-13; design (B) of
`/bigtemp/vnr3ne/analysis/solr-2026-10-12/design-z2-f2-decoded-state.md`).** A decode outside every region keeps its
minted leaves' symbols in the parsed tree, but a field the system derives from one there (`Replica.<init>`'s
`State.getState(String.valueOf(..).toUpperCase())`) is a plain constant: no VM model runs without the region's shadow
stack. Today a case declares the classes that build its view (solr-18413: `ClusterState`, `DocCollection`, `Slice`; solr-bugs-snapshot-no-active: those and `Replica`, whose lookup and construction paths multiplied its round 1 1700-fold, held at world depth 0). The general
fix: the adapter's decode bracket (`MessageDoors.decoded` / `jsonRead` of a fetch) opens a tracking activation, so every
decoded product's derived fields carry their expressions whatever the case's scope -- a VM/runtime change (a shadow
stack on a role thread, its writes attributed to the decoding occurrence) with an identity design first.
