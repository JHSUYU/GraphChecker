# TODO: the old HDFS bugs (system/hdfs-buggy-detect) and HDFS (system/hdfs-liftlab, THE HDFS branch)

Order:
0. The old bugs (section "Buggy-detect"): round B1 on liftlab, then what HDFS-14311 and the dropped case leave.
1. HDFS on liftlab (section "HDFS on liftlab"): the series H1 is done (2026-10-27, STATE §L, `results/hdfs/`) and the
   branch is pushed (a3e1881d5); what is left are the port's open items below.
2. HDFS's former bodies (STATE §0): their follow-up items below are optional engine work, done when a case needs them or
   before a clean final acceptance run; any change goes on this branch and is judged by its cases.
3. The cross-cutting engine items (last section), when a system needs them.

HBase, ZooKeeper and Solr are finished; each one's plan is its own branch's TODO (`system/hbase`, `system/zookeeper`,
`system/solr`), and each old-bug branch's open items are in its own docs (`system/<x>-buggy-detect`); a "TODO HBase
<n>" or "TODO Solr ..." that STATUS, the design or the check tables cite is that item of `system/hbase`'s or
`system/solr`'s TODO. The owner:
"hdfs所有的case跑完为一组，不要有回归。然后就到另一个系统". Each system is finished when every one of its checks has an exported
`.smt` that is right (SAT confirmed, or UNSAT at the fixed point) and every known bug of it passes. Branch, tree and path
details are in [STATE.md](STATE.md); every check with its state in [../checks/README.md](../checks/README.md) and its
reading in [../STATUS.md](../STATUS.md); commands in [OPERATIONS.md](OPERATIONS.md); speed and the cluster in
[../design/PERFORMANCE.md](../design/PERFORMANCE.md).

## Injected bugs (`system/hdfs-injected`, 2026-10-30): not started

The whole work order is [INJECTED-BUGS.md](INJECTED-BUGS.md): this system's five cases (§3), and the shared
procedure, acceptance and results table.

## Buggy-detect (this branch, `system/hdfs-buggy-detect`)

STATE §B and START-HERE §0 have where everything is; [BUGGY-DETECT.md](BUGGY-DETECT.md) the table and the owner's
decisions. The other systems' old-bug items are on their own `system/<x>-buggy-detect` branches.
1. **Round B1** (liftlab, from 2026-10-28 00:07: the seven cases at once, `accept-B1-buggy-<jira>`): B1: the six detected cases SAT again, CONFIRM, native 10/10, control 0/10, report.py PASS (results/hdfs-buggy/); HDFS-14311 not detected again (UNSAT_CLOSED, substantive: 9 paths, 8 free; 2333 s).
   Read each by BUGGY-DETECT's standard (CONFIRM in the VM, native k/N with control 0/N, report.py PASS, the chain against
   the case README's), then fill BUGGY-DETECT's B1 column and each case README's result; a verdict that differs from the
   CloudLab row is read before it counts.
2. **HDFS-14311's remaining blockers** (closed by the owner as a capability limit, 2026-10-27; reopen only with the
   owner's OK): the carried-anchor concurrency that offers the reader's own task, created after the read, as a writer;
   CONFIRM's pairing hold sitting after the reads that decide the guard; an ORDER timeout after the fatal refutes in
   Confirmation (changing it needs the owner's sign-off). Evidence: the case README (B14311a-f).
3. **`hdfs-buggy-15590`**, dropped by the owner (its witness fires another throw than the point's own), is still a case
   directory and a `report.py` row on this branch; its tree branch `graphchecker/hdfs-bug-15590` was never pushed, so it
   cannot run from GitHub. Delete it, or keep it as a record (the owner's call).
4. **`hdfs-buggy-cases.tsv`'s header** names the source list by its CloudLab path; fix it with the next change to that file.
5. **A fresh clone runs the old bugs**: check REPRODUCE §7 from GitHub alone, as TODO "HDFS on liftlab" 4 for the ad hoc
   cases.

## HDFS on liftlab (`system/hdfs-liftlab`)

The series H1 (the 45 cases but hdfs-11741, each alone on the 12 reachable lifts) is done: 62555 s (17.4 h), each SAT
read with `smt-legend.py` and each UNSAT with `vacuity.py` (CHECKING §1; `results/hdfs/README.md`). What the port left open, each with its evidence (`results/hdfs/README.md` has each case; the
F, C, D, L and P runs named below are the port's CloudLab rounds, whose record is the tag `archive/system/hdfs-cloudlab`).
STATUS and `results/hdfs` cite these numbers:
1. **hdfs-17897's replay race** (F1 and H1 confirmed it, 10/10; the race remains). The fatal of dn0's heartbeat-fault
   world is observed in some replays and not others: C3-17897 observed it (session 344f), DD1 did not (the test passed),
   and then the composed formula holds the fault valuations UNSAT and DECIDE has only the faultless pairing claims, each
   refuted by CONFIRM (8 of 8 in DD1). Natively EX1 reproduced it 10/10. Look at which order in the striped-checksum
   client decides it; a run where no explored world observes the fatal is a race, not a verdict.
2. **hdfs-adhoc-28/29's seed replay under load** (done by a tree workaround, a2038d083d7 + 0d2b473db63: the live
   replica not yet tried with the least DataNode UUID is the primary). Why the write pipeline's order still differs
   between a recording and its replay (F2-adhoc-29) is open (STATUS defect 40).
3. **DECIDE's nested own arms** (agent D): the order dependence when a nested family is first closed under another
   session's scope (PIPELINE §9, measured zero on C1 and C3); the plant-writer seed (`recordedAtPlants`) and view-version
   families are not owned (reviewer's follow-ups).
4. **A fresh clone runs the series** (owner: push so that a clone reproduces): check REPRODUCE §0-§5 from GitHub alone (an
   empty `GC_TREES`, the fork's branches, the build, every case valid, one case to its verdict), as `system/hbase`'s
   REPRODUCE was checked on 2026-10-22. Not yet done for this branch.
5. **The CloudLab setup scripts left on this branch** (done 2026-10-28, 294f04cdd): `tools/cloudlab/` and
   `tools/vm/build-image-docker.sh` are deleted; gc-env's default `LIFTS` is the 11 reachable workers (no lift07, lift11,
   lift15).
6. **The own-witness pass and equal planted skews** on consecutive cells of one clock (the second jump is 0 and drops out of
   movedRoots): the own claim is lost, never wrong (PIPELINE §9).
7. **The canonical witness** (agent D, branch `hdfs-decide` 1d70822bd, built and unit-tested, not reviewed, never pushed:
   the commit is not in this repository): DECIDE claims a re-pairing model z3 answered with arbitrary clock jumps and
   re-pairings outside the cone (17897 DD1: eight claims each with 10-13 jumps, each refused by CONFIRM for those parts);
   `ClaimPolicy#canonical` would hold a witness to its least clocks and its fewest re-pairings within a sixth of the decide
   budget. Not needed by the final rounds (17897 F1 and H1: MARKER_FLIPPED, confirmed, 10/10).
8. **`replay_timeout_s`** is 2400 s; hdfs-adhoc-24/26/37 declare 7200 (their focused replays run the whole upgrade or
   rollback test). A general rule would bound a focused replay by the seed replay's own measured time.
9. **A consumer named by arrival paired with another handle-paired send** (hdfs-adhoc-11 F1, investigator 2026-10-24):
   dn0's SASL consumer is the k-th accepted connection, so a race that adds or drops a client retry before it pairs it
   with another send (TOPOLOGY_DIVERGENCE "a replacement, not growth"); a handle-paired attach (each SASL message carries
   its `hdfs-sasl-<uuid>`) could be a second slot or a DIAGNOSTIC in `SlotTable#replaced`/`#take`, or the region where
   SaslDataTransferServer receives the handshake could open under the SASL anchor (`DataTransferSaslUtil#inboundSasl`).
   The tree avoids it for 11 (no block-acquire retries).
10. **A replay that ends at its witness before a planted root's mint** (agent D's design C, deferred): 11741's obligation
   0088b8 reached the fatal and ended AT_WITNESS before the balancer's second pending move minted the door root its parent
   world planted, so `FocusedReplay` (:672 at 9c1bbe157) refused it for the missing mint; such a run could name the roots it
   never minted and keep only the minted ones in its world (`Corpus.world`), CONFIRM re-planting strictly.
11. **DECIDE's budget on large corpora**: 52's 128 valuations each timed out path by path (a scoped path ask ran up to
   ~1390 s) and the composer's own whole one-shot ask ran out of memory at 292 s, while the exported file is unsat in 35 s
   under `tools/lib/z3-race.sh` (4 GB per engine). Why the composer's one-shot differs from the race (options, model
   symbols, its room) is open.
12. **hdfs-11741's native plant** (F7, F8; 11741 is not in H1, owner): every confirmed CLOCK_SKEW claim reproduced 0 of 10 natively; the five clocks
   were planted, the two ORDER rows on dn1's `removeExpiredKeys` occurrence (653dbe1f..., before the balancer's
   6306493a...) never came (`reproduce/run-*/answer.json` `NOT_REACHED`). system/hdfs's 10/10 also applied the
   serial-number hook; here SERIAL_NO stays at its recording and is not planted. Read which native occurrence runs dn1's
   key removal and whether the order's identity or the unplanted serial number keeps it apart.
13. **One unrun heartbeat occurrence withholds a confirmed SAT** (P1-17967-pathC, P2-17967-pathB, P2-17967-pathC,
   all confirmed in the VM and reproduced 10/10 natively): one EXPLORE gap, TOPOLOGY_DIVERGENCE (P1: the heartbeat
   ran under a `BP_SERVICE_ACTOR` anchor, not the closure's heartbeat anchor) or ADMISSION_GAP (P2: "no session of
   this corpus ran this occurrence"), BLOCKING, so report.py withholds the claim. The timing of the DataNodes'
   heartbeats against their service actors varies more under heavy CPU load; P3 and H1 passed them. Read whether an
   occurrence off the claim's cone should block a SAT (CHECKING §1).

## HDFS: the former bodies' open items (`system/hdfs`, `system/hdfs1`; trees r7, r7-21, r8, 11741-r6; image `vm-hg5`)

The items below name the former bodies' code (2026-10-08); the engine has since been rewritten (`system/solr`,
`system/hbase`). Read the current code before taking one; any change goes on `system/hdfs-liftlab` and is judged by its
cases. 46 of 46 cases closed with a hand-read `.smt` (STATUS "HDFS checks"); no new bug. The two-phase final acceptance
run once planned here (owner 2026-10-06) was carried out as series H1 on this branch. What is left is the general work the
workarounds stand in for, the defects the session found, and the cleanup. None of it reopens a closed case unless a
change alters its formula (one change per round, RULES "Lock, then one change at a time").
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
inherits a flip the session does not state: W21 (`hdfs-21w/accept-W21`, no longer on disk), BLOCKING EXPLORE
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
- **Scope (B)**, widening that would only make right formulas more flippable: 29/30 the block-pool map written at
  DataNode start-up and `bpServiceToActive`'s in-window writer gated by HA state; 17's lease and 39's IBR ordering
  (turns on threads with no schedule events); an identity compare of a tracked reference with an enum constant states
  no VM term (VM.md §5.2); 05's thread-local buffer invariant; String fields (21's versions; defect 34); 14's retry
  identity and its constant arm; 11's u18#3 key gap; 20's txid.
- A possible flake: Mockito `UnfinishedStubbingException` in `TestBlockRecovery2`.

### 6. Speed (PERFORMANCE.md §5)
- **Incremental planning** (owner 2026-10-07: "这个优化记做todo吧"; the first speed item): merged on
  `system/solr` (7e7bb64c2, 2026-10-08), so on this branch too. One planner JVM serves an exploration's rounds (`ExploreMain --serve`,
  PIPELINE §7.1/§7.9), keeping the corpus's rows with what each session's rows alone give, the static map and the
  slot table, whose rounds write only their changes; within a round `dependence` and the closure's re-walked
  pieces are computed once. Gate `offline-ab.sh` `EXPLORE.serve` identical on EX1 07e, 11741, 09, 17899-bug2, 39
  and SC1 solr-18406/18413 (07e: 2960 s fresh against 1667 s served, late rounds 300-360 against 150-180 s;
  PERFORMANCE §5 item 0). Live (`solr-incr-plan`): INC1-adhoc-09 UNSAT_CLOSED as EX1,
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

## Cross-cutting (engine), when a system needs it

**Force the fatal arm inside the target region: done** (owner 2026-10-08; merged on `system/solr` fa70dae08, so on this
branch; PIPELINE §5, §7.10, §8). Left: `seedFlipsAfterForcedFlip` was 0 in every Solr run of agent F2, so the seed path's
anchor flips and open-arm asks may be deletable (decide on measured numbers).

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
