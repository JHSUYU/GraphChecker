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

## Solr (in progress; `system/solr` `8bd4a0cfb` + the handover docs, worktree `/bigtemp/vnr3ne/wt/gc-solr`; owner stop and handover 2026-10-12 ~14:00)

**Read first:** STATE.md §S, then this section top to bottom, then the agents' own reports
`/bigtemp/vnr3ne/analysis/solr-2026-10-11/HANDOVER-2026-10-12.md` (heads, gates, run dirs, gotchas per branch), the
reading checklist `.../SG3-reading-checklist.md`, and STATUS "Solr checks". Nothing runs; every branch is committed;
nothing is pushed.

**Goal** (owner 2026-10-08, restated 2026-10-11 /goal): the 20 Solr cases each get an `.smt` whose causal chain is right.
- The 8 bug checks end `SAT_CANDIDATE`: the witness confirmed by a CONFIRM replay, reproduced natively (>= 1/10), and the
  `.smt`'s chain is the bug's chain (read against 8.11.4, CHECKING.md).
- The 12 study checks (05 07 09 10 13 14 19 21 31 38 39 40): a SAT is confirmed, an UNSAT stands at its true fixed point
  (BOUNDED does not count). A study SAT that passes validation is a new-bug candidate: realism, JIRA, STATUS.
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

### 1. Branches in flight (committed, not merged, not pushed). Merge in this order

| # | branch | head | Solr tree branch (built worktree) | state | left before its merge |
| --- | --- | --- | --- | --- | --- |
| 1 | `solr-zk-doors` (READ doors + R4) | 9f0b81058 | `gc/solr-zk-doors-r` 2346cafecd (`/bigtemp/vnr3ne/wt/lucene-solr-zkdoors-r`) | **MERGED** into system/solr edc62b76b (2026-10-12) after the canaries Z1W (gc-out/solr-zk-doors): restore and reindex PASS native 10/10; lock-leak SAT confirmed native 10/10 by another world (an HTTP reload failure, a reported FAILED status; STATUS row) | a full 40 (gate (d)): round LD1, `~/gc-run/ld1` (edc62b76b, cases on lucene-solr-zkdoors-r), CASE_TIMEOUT_SECONDS=21600, gc-out/solr; lock-leak's workload stops at a FAILED status (gc/solr-final, SG3) |
| 2 | `solr-explore2` (EX) | fe8c7434f | (none; ib-trees for its gates) | reviewed three times through 70f177ddd; offline 07 re-asks 2176 -> 788, 21 785 -> 350; live 21 ids/arm 12.2 -> 6.9 -> 3.2 but in flight flat (~650) | reviewer re-check of 70f177ddd..fe8c7434f (RunSpellings, `Class@#`, handles by class); offline gate + canaries on fe8c7434f; live 21 (10800) and 07 (21600) from `~/gc-run/rx7`; if they still do not drain, read which arms stay in flight before more key changes; decide `?[]` |
| 3 | `solr-zk2` (Z2) | fcec19075 (system/solr c622a4740 merged) | `gc/solr-zk2-next` b2605b6bd7 (`/bigtemp/vnr3ne/wt/pno-trees2/lucene-solr-checks`; lacks zk-doors' read hooks, unplaced there) | 2026-10-12 (agent Z2, second session): the WIP enum compare completed and narrowed (joinable, unstated version: 6e50f8e80); review re-checks fixed (4a63c68b0, b9bc358a5, 53c512a9e: refresh reach, row order (seq, tie) with RowOrder at every engine-read cut, view writer spelling, store write positioned before filing, world-pairing claim = the session's whole world with its fatal-path clause, no engine door throws into Solr); char-range assertions replaced by z3's bmp alphabet (f6f35d191, Z2K snapshot formula sat in 1.8 s); String.valueOf lowered; store content exports imported through the VM's expression store; rule (a) (14848540c), then the final re-review (B-a: a leaf of a producer refused by rule settles by that producer's own export -- EXPORTED, CONSTANT, BOUNDED with the named `daemon_tick_bound`, open with none; M-b: every door catches and names an engine fault, ENGINE_FAULT, and the pre-window cap names what it dropped; M-c: an engine-write cut is (seq, tie); an answered String arrival is the solver's literal, an arrival its text). tra Z2S (z2-16): SAT confirmed, native 10/10, FORMULA_SAT (fixed in 14848540c: offersArms); 18413 Z2R: CLOCK_SKEW witness, chain open on state.json leaves (export bug + tick bound, fixed); snapshot Z2S: no witness, closure truncated at the task bound; Z2T died on pno-trees2 (DOOR_METHOD_UNAVAILABLE), Z2U (z2-17, sg3-trees) running | rerun after the final re-review: 18413 x2, snapshot, tra (GC_TREES sg3-trees); the lead's review of the final diff; merge |
| -- | `solr-sg3` (dry-run integration) | 2ca18a2b5 | `gc/solr-final` 86f762adb1 (`/bigtemp/vnr3ne/wt/lucene-solr-final`, built vs sg3's jar) | system/solr 8bd4a0cfb + explore2 fe8c7434f + zk-doors 9f0b81058 + zk2 29d61a059, unit+shell green; seed_replay_time_factor=130 in the four Solr workflow.properties; natives 18406/18413 PASSED, 15 workloads not run | NOT the merge of record: re-merge as branches 1-3 land; rebuild gc/solr-final against its jar; run the other 15 natives |

Every other `solr-*` branch is merged or superseded.

### 2. ZooKeeper READ doors (owner priority 2026-10-09) -- state 2026-10-12

Why (unchanged): an external study's two Solr failures (solr-adhoc-40 `RoutedAliasUpdateProcessor:133`, solr-adhoc-09
`DeleteReplicaCmd:278`) share one root cause still in main: a watch callback whose re-read fails with ConnectionLoss or
SessionExpired only logs and never re-arms (`ZkStateReader.AliasesManager#process`, `StateWatcher#refreshAndWatch`);
JIRA has no report (SOLR-16257 differs; SOLR-12256/12261/4739 related).

Built (branch 1 above): DATA_FLOW catalog rows for ZooKeeper getData/exists/getChildren; HOOK `before`; the read marker
roots no region; flippable only on the demanded data flow (a PROVENANCE fetch, or a LOCATION fetch at a version up to the
one read, on the reader's node); the lost reply as a Solr-tree workaround: getData's door after the reply
(`SolrZkClient#causynthReplied`), the fault arm marks (watcher, path) lost and `ProcessWatchWithExecutor#process` drops
that watcher's next DATA event (a real lost reply registers no client watch; healed by a later getData/exists whose reply
arrives). 40 declares node2's first target occurrence (the very first update lands on node0 or node2 by a leader race;
on node0 no fetch lies on the flow). Gate (b) passed (2 data-flow doors asked, both node2's aliases re-reads). Gate (d)
open: a full 40 -- a witness by a read fault at node2's aliases fetch, confirmed + native >= 1/10 = the external study's
lost-watch candidate, rediscovered (then realism + STATUS + docs/checks/new-bugs.txt). 09 additionally needs the
timed-wait door (merged) -- its expected SAT is a FAULT:TIMED_WAIT root on a grown invocation (checklist).

R4 (on branch 1): control producers and store fetches run doors-only (VM paused except at their door decisions;
container mutations at scope-map sites stay hooked); a value demand on one unpauses it through GROW; seed-only ones are
BLOCKING at the fixed point.

### 3. Open problems (each with its evidence)

- **a. EX convergence (07, 21, and 05/31/39 which grow the same way):** after the key fixes and the spelling map, live 21
  still had ~650 in flight not draining at rounds 28-33 (RX3, 3.2 ids per arm); the remaining key differences are world
  and timing differences (whether a watcher member or a client STATUS ran; conditional writes; `?[]` vs `?[value]`).
  Evidence `/bigtemp/vnr3ne/gc-out/solr-explore2/accept-RX{1,2,3}-*`. Owner rule: a genuinely large closure converges
  with resources (21600 s for 07), redundant depth is a defect.
- **b. 18413 on Z2:** content capture does not reach node1's RoutingRule (built outside every region) -> WIRE_FLOW kept;
  then the witness path was refused on `"ACTIVE".equals(<enum read>)`, WIP fix 7023c526b. 18413 must pass on Z2 twice.
- **c. 18413 CONFIRM fragility on trees without Z1's hooks** (ib-trees: TW1/TW3 refuted "WIRE ab157e968b0f6be3 ... never
  attached": node1's watcher folds two routing-rule writes into one fetch); on z1-trees (TW4, TW5) it confirmed. The final
  tree has Z1's hooks; watch it in SG3 (two runs if it fails once).
- **d. snapshot-no-active:** new workload (ADDREPLICA late, use.perreplica=false) never run on b67225114; Z2K's COMPOSE was
  undecided (53 paths, 44 MB -> 16 MB with define-fun sharing; 13,188 unguarded char-range assertions remain).
- **e. Seed time on a loaded cluster:** 40's seed 2169 s vs its 2400 s bound; 13's seed was compute-bound (workaround in
  the final tree). SG3 runs with `seed_replay_time_factor=130` (solr-sg3; recordings 19-37 s -> 2500-4800 s), which
  leaves obligation replays at replay_timeout_s 2400.
- **f. 09:** needs the timed-wait door (merged) and EX; its workload exists only in the final tree.
- **g. New-bug candidates:** (1) 19, a stale cluster-property view at core creation (F2V4 session `0c227a75f31cbf87-
  7ca7ab71`), needs Z2's legacyCloud leaf; (2) the lost watch (§2) via 40/09.
- **h. 31 and 39:** seeds match with Root:WAKE; the frontier-side turn drift (25-38 % of their stall time) is open and was
  not approved; never run whole (they grow like 07/21 -> EX).

### 4. The final round (SG3) and the fork

1. Merge §1's branches 1-3 into system/solr in order, each after its own gate (re-run the shell test + mvn after every
   merge; resolve conflicts as solr-sg3 did -- its commit messages list the decisions: RootMint's unplanned rule via
   `LibraryCatalog.rootsNothing`, ClosurePlanner's Demand `why` + `value` flag, GROW drops doors-only marks before the
   plan, doors.jsonl with Z2's write hooks and Z1's read hooks, SessionManifest with runSpellings and doorsOnly).
   Carry `seed_replay_time_factor=130` (solr-sg3's last commit) into system/solr.
2. The final tree: `gc/solr-final` (`/bigtemp/vnr3ne/wt/lucene-solr-final`) = gc/solr-zk-next 22930889c8 + gc/solr-zk-doors-r
   2346cafecd + gc/solr-zk2-next b2605b6bd7 + 13's workarounds; merge any later tree commits of the agents' branches;
   build it against the merged engine head's jar (`experiments/solr/build.sh`, Java 8; never while a run reads it); run
   all 20 cases' workloads natively once (every junit report present; `experiments/lib/run.sh <dir> <arg> validate`).
   Point the cases at it: `GC_TREES` with a `lucene-solr-checks` link to it (as `/bigtemp/vnr3ne/wt/sg3-trees`).
3. Round SG3: all 20 through `tools/adhoc/sweep.sh` (2 heads per host, `CASE_TIMEOUT_SECONDS=10800`; 07 and 14 need
   21600/14400: rerun a cut case from its jobs line), vm-force5, PRUNE=0. Verify with `tools/rounds/round-verify.sh`.
   Read every `.smt` with `tools/analysis/smt-legend.py --repo /bigtemp/vnr3ne/wt/lucene-solr-final` against the
   checklist (`/bigtemp/vnr3ne/analysis/solr-2026-10-11/SG3-reading-checklist.md`) and CHECKING §2; write each STATUS
   row; record every FP filtered ("COMPOSE SAT -> CONFIRM refute -> excluded -> UNSAT_CLOSED"). The lead's pre-readings of
   the bug checks' chains are in `/bigtemp/vnr3ne/analysis/solr-2026-10-11/readings/` (lock-leak, restore, reindex,
   snapshot).
4. The fork: push `gc/solr-final` as `graphchecker/solr-checks` to `https://github.com/JHSUYU/solr.git` (never apache).
   trees.tsv, solr-cases.tsv (07's budget 21600) and REPRODUCE §6 are drafted (solr-study2); verify §6 from a fresh clone
   of `system/solr` + the fork once both are pushed (pushing `system/solr` needs the owner).

### 5. Where things live

- Lead logs: memory `lead-session-2026-10-11-solr` (this session), `lead-session-2026-10-08-solr` (before).
- Agents' reports: `/bigtemp/vnr3ne/analysis/solr-2026-10-11/HANDOVER-2026-10-12.md` (this stop),
  `/bigtemp/vnr3ne/analysis/solr-2026-10-08/HANDOVER-2026-10-09.md` (the previous stop).
- Briefs, designs, notes (2026-10-11/12): `/bigtemp/vnr3ne/analysis/solr-2026-10-11/` -- AGENT-RULES.md, brief-{z1,
  zkdoors,z2,study,explore-redundancy}.md, design-explore-key.md, IB1-notes.md (rounds IB1, IB2, IZ1, IS1),
  SG3-reading-checklist.md, readings/, ex/ (DepDiag), rd-harness/.
- Lead rounds: `/bigtemp/vnr3ne/gc-out/solr` (IB1, IB2, IZ1, IS1; rep/ = reproduce-again of 18413).
- Agents' rounds: `gc-out/solr-zk` (Z1: Y*), `gc-out/solr-zk-doors` (Z1's READ doors: Z1*), `gc-out/solr-zk2` (Z2:
  Z2*), `gc-out/solr-study` (ST: ST*, SF*, TW*, SC*), `gc-out/solr-explore2` (RD: RX*). Keep lists per agent in the
  HANDOVER file.
- Trees (GC_TREES dirs): `ib-trees` -> lucene-solr-body (gc/solr-body, all 17 workloads, no Z1 hooks); `z1-trees` ->
  lucene-solr-zk2 (gc/solr-zk-next 22930889c8, bug-check workloads only); `zkdoors-trees` / snapshot repo= ->
  lucene-solr-zkdoors-r; `pno-trees2` (gc/solr-zk2-next); `sg3-trees` -> lucene-solr-final (gc/solr-final).
- Snapshots worth keeping: `~/gc-run/ib1`, `ib2`, `z1d-8`, `rx7`, `z2-13`, `st20`; the rest of this session's
  (`z1-*`, `z1d-1..7`, `rx0..6`, `z2-1..12`, `st1..19`, `ib1n`) can go after a pgrep on all lifts.
- Gotchas (this session): pass a sha to tools/lib/worktree-add.sh (it resolves in ~/GraphChecker); never `git worktree
  add` without it (a full checkout writes third_party to NFS); `launch-round.sh` does not pass CASE_TIMEOUT_SECONDS over
  ssh (launch-run.sh with the variables on the command line); stop-run.sh alone on its command line, by round suffix,
  with the run's GC_OUT; an agent listed as running may be idle (compare last commits); the account's usage limit can
  stop agents mid-edit (resume each with SendMessage).

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
