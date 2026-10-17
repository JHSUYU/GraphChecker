# GraphChecker optimizations: what was done, what it bought, what is still owed (2026-10-16)

The owner asked for one document of every optimization so far -- the parallel ones, the ZooKeeper ones, and the
ones designed but not done -- as the starting point of the HBase port, where the code is to be refactored
thoroughly and these optimizations completed. Solr stays as it is after its final round (owner 2026-10-16).

Each row says the problem as measured, the mechanism, where it lives (commit on `system/solr`), and what it bought.
Numbers are from the Solr final rounds SGF7/SGF8 (`gc-out/solr/accept-<round>-<case>`) unless named otherwise.

## 0. Where the time goes in one case, and what bounds it

A case is SEED (static passes, the recording, the seed replay), EXPLORE (rounds of flips: planner -> solver ->
focused replays, plus GROW), COMPOSE (one formula, decided by z3), CONFIRM/EMIT/REPRODUCE.

- **Pool-wide already before 2026-10-16:** EXPLORE's replays and solves (a stream over every host of `LIFTS`, the
  host ledger at 70 % of each host, host solvers serving questions, the hard lane), REPRODUCE's native runs.
- **One host:** the static passes, the recording, the seed replay, each round's planner, the composer; these are
  the critical path once the pool is wide enough (Amdahl). adhoc-10 SGF7: ~73 % of its 10228 s ran on one host.
- **What a replay costs:** the concolic VM is OpenJDK 8 Zero (interpreted, no JIT), ~1.2-1.4 cores per replay,
  RSS 0.4-0.8 GB mid-life and 1-2.5 GB at its end (publication). The engine's own code in the replay JVM (row
  publication) is interpreted too.

## 1. Parallelism and memory (done)

| # | Problem (measured) | Mechanism | Code | Effect |
|---|---|---|---|---|
| 1.1 | The final decide ran 1 pair of z3s beside a 16 GB composer (SGF7 adhoc-10: 315 z3 runs, 30 timeouts, the 1800 s budget spent with questions unasked) while 12 hosts idled | The final COMPOSE's scoped z3 pairs also run on every other pool host over ssh: the shell charges whole 2048 MB pairs of each host's ledger room (at most 16 GB a host) for the composer's life; a remote z3 prints its pid, reads the shared part from one file beside the query (links are 1 Gb/s), is signalled and killed over ssh; a host that never read its part gives its questions back; the path asks at once follow the pairs placed | `ComposeMain --z3-hosts`, `smt/Z3Incremental`, `compose/Disjunction`, `run_engine.sh campaign_z3_hosts_grant` (6c762ff49, cc110c7d3) | SGF7B adhoc-10: decide 1800 s (cut) -> 250 s, 544 z3 runs, nothing unasked |
| 1.2 | The composer started at 4 GB and doubled on each out-of-heap exit, re-reading the corpus each time (adhoc-10: 4 -> 8 -> 16 GB, 818 s lost) | A composer's heap is its corpus's, as a solver's: 1.5 x the session files, at least 4 GB, at most the engine heap | `run_engine.sh do_compose` (cc110c7d3) | no restarts since |
| 1.3 | A JVM that collects over a full old generation never ends (the overhead limit needs eden < limit, which a full GC empties); a planner thrashed 30+ min | `contract.HeapWatch`: >= 50 % of a 60 s window in GC and old gen >= 90 % after the last sweep -> exit 3 (the out-of-heap status, restart at 2x) | ExploreMain/ComposeMain/ObligationSolverMain (70a24928f) | thrash ends within ~1-2 min |
| 1.4 | A stop other than a witness (planner out of heap) let replays and hard-lane asks drain unbudgeted; the case timeout killed the campaign before COMPOSE (SGF7 adhoc-40: no claim) | The campaign budget ends any drain but a witness's; the stop becomes `CAMPAIGN_BUDGET_REACHED` naming the earlier one | `run_engine.sh campaign_explore` (b863cd6c7) | 19 SGF8 ended at its bound with a verdict |
| 1.5 | Replays were charged their peak's 90th percentile for their whole life; a replay peaks only in its last read (publication: heap 350 -> 890 MB); a lift's ledger held 19840 MB over 4831 MB of real use | A stream replay is charged the 90th percentile of the replays' life-mean RSS (`workload_rss_mean_mb`); each admission keeps uncharged room for 4 end peaks (p90 peak - charge); the growth is charged as it grows | `campaign_replay_typical`, `campaign_host_try_start` spare (4ac570330) | SGF8 19: 768 MB charged vs 1408 before |
| 1.6 | The served planner's heap filled on big corpora (adhoc-10 at 16 GB, round 12; adhoc-40 at 91 min) | A lowering frame holds its committed side conditions by reference (no copies); a session's leaf sets are arrays over one instance of each name | `compose/SmtLowering.Conditions`, `explore/Corpus.HeldLeaves` (2385d07fe, 64178b266) | live set -30..38 % (adhoc-10/-40 subsets), outputs byte-identical on 5 corpora |
| 1.7 | The composer spent 870 of 1032 s in its roots' domains: each root's `comparedLiterals` walked every decision's term again | Root symbol -> the predicate decisions reaching it, indexed once | `explore/Corpus#deciding` (c92b8b1ca) | adhoc-10: 891 -> 52 s, adhoc-09's candidate byte-identical |
| 1.8 | Smaller ones of 2026-10-16's night | a replay with nothing new for 300 s ends (2c645fb47); a view republished at its next version is no progress (825afab33); CONFIRM ends at its first mismatch (bad02c271); an open-chain witness is confirmed first, its chain grown meanwhile (63abbf77d, 2f49cea32) | | each removed a 10-40 min tail |
| 1.9 | SGF8 adhoc-14: the served planner and then the composer ran out of heap at the engine heap 16384 MB (27 GB corpus, 429 sessions, 353 paths) | The Solr study checks' engine heap is 20000 MB (`engine_memory_mb`): a lift has 31583 MB, 70 % is 22108, the engine's footprint at 20000 is 21634 plus a z3 room | `experiments/solr/solr-adhoc/workflow.properties` (solr-heap20) | see 5.15 for what fills it |
| 1.10 | A host solver lived 2 h past its run's end holding 1.2 GB and its ledger charge (lift04, SGF8 adhoc-14): an earlier run of the same corpus path was stopped mid-answer, its `.taken` question stayed, and an idle solver never retired while a question was taken | A solver answers one question at a time, so a question taken when it is idle is a dead solver's, its asker's to fail: `Service#retire` waits only on questions still asked | `explore/Service` (solr-heap20) | no solver outlives its run |
| 1.11 | The composer kept every subterm its lowering minted to its last path (what each field reaches, walked in the composer between paths, SGF8OOM-adhoc-14's 26-session subset after 20 paths: `SmtLowering` 1195 MB, of it the shared subterms 582 MB and their mints in `SmtSymbolTable` 462 MB, against a 57 MB body; its whole corpus >400 MB a path, the heap bound after 6 of 353 paths) | Between paths a subterm no statement (or cell a box reads back) reaches is dropped with its mint; one map by name (prefix + identity digest), so a subterm lowered again has its old name and the body is byte-identical | `compose/SmtLowering#path`, `#unstatedDropped` (solr-compmem) | Subset: lowering 289 MB after 20 paths, peak live 4583 -> 2462 MB (small-ab measure), loop 300 -> 263 s; whole corpus at 20 GB ~110 MB a path instead of >400, 27 of 353 paths composed before the bound instead of 6, 48 s a path instead of 64; candidate body and manifest rows byte-identical (subset, 20 paths; corpus at 6) |
| 1.12 | GROW wove every generation that added task rows, a fixed 62-64 s in the head's hands (no start dispatched meanwhile): SGF8 adhoc-19, 11 weaves, 8 of them byte-identical to the tree before (offline re-weaves of g4, g5 and g11 identical; g3 and g4 differ in one class): their new rows were more occurrences of regions whose hooks were woven (`ZkDistributedQueue.peekElements` wakes). The weave's 54 s JVM is Soot's: class resolution from the classpath ~45 %, the jb bodies ~40 %, writing ~10 %; the plan-dependent weave ~2-3 s (jstack samples) | A plan's weave key (`causynth.WeaveKey`: every task's `InstrumentationPlan` by value, a repeated one once -- what the weave reads of a plan); GROW weaves only where the key is not its tree's, else keeps the tree. Replaces the row-count rule (more rows = weave) | `run_engine.sh campaign_weave_key`, `campaign_stream_grow`, `campaign_instrument` (`weave_key` beside a tree); `causynth/ConcolicInstrumentationSelections#weaveKeyFromEnvironment`, `causynth/WeaveKey` (solr-grow) | 19: keys g1=g2, g3, g4=...=g11 (exactly the identical weaves); 8 x ~63 s = ~500 s off GROW's serial chain (9 % of 19's EXPLORE); the key 0.3-0.8 s, 0.34 GB |

## 2. Replay fidelity and the schedule (done)

| # | Problem | Mechanism | Code | Effect |
|---|---|---|---|---|
| 2.1 | The Overseer's `peekElements` loop counts its wakes (`Root:WAKE/<wait>#k`, a timing count); a replay's k-th turn is another turn than the recording's, so its events found no slot and the watchdog gave slots up (adhoc-10's seed: 320 stalls, 611 s window for a 52 s recording) | A timed-wait loop's events take their turn family's slots in recorded order, and its reads take none (the polls' count is the loop's timing; the writes order what it finds) | `runtime/ScheduleLog#turnFamily` (afb39c7e6, 19ae623a7; owner-approved: semantic counts only) | a focused replay 446 -> 350 s, its WAKE-turn divergences 67 -> 2 |
| 2.2 | Two timing choices in the Solr tree: the test client's live nodes in a HashSet of `host:port` (which node its CLUSTERSTATUS sticks to follows the random ports); `ZkStateWriter#maybeFlushAfter`'s nanoTime moves the Overseer's queue removal between the turn and the state-update tick | Tree `gc/solr-zktrace2` 12d23091d1: live nodes in node order (`CausynthRandom#order`); an unbatched Overseer removes each message's queue item in its own turn | fork `JHSUYU/solr graphchecker/solr-checks` | adhoc-10's seed: stalls 107 -> 22-33, window 574 -> 407-489 s, recorded occurrences reproduced 727 -> 860-912 |

## 3. Exploration rules (done)

| # | Problem | Mechanism | Code | Effect |
|---|---|---|---|---|
| 3.1 | Every fault door of the closure was flipped, the test client's own ZooKeeper calls too (configset upload, `makePath`): SGF7 round 0 of 10/39/40, 276 such flips, none of whose replays ran the declared occurrence (the test failed in its setup); every fault root of the five Solr fault bugs is a server's ZK write or the client's request | In the workload client's root contexts only the doors of the system's named transports fail (Solr: `SOLR_HTTP`, `SOLR_HTTP2`) | `explore/ClientFaults`, `system.sh client_fault_transports` (4c001b0bf) | ~25 % of those rounds' replays |
| 3.2 | A heavy region planned whole: seven `CoreContainer.create` (14's SplitShard sub-shard cores, for the `inFlightCreations` set they add to and remove from) wrote 109,222 rows, 89 % of a 499 MB seed session; seed replay 36 min against 9.5 | A region root the system declares (`doors_only_roots`) runs for its doors alone in every plan; the mark (`doorsOnlyDeclared`) reaches the task rows, EXPLORE never unpauses it, GROW's rows get it too | `plan/DoorsOnlyRoots`, `RuntimeSelectedRegionFinalizer#stateDoorsOnly`, `ClosurePlanner`, `ExposedRegionPlanMain` (b48388754, 5c5ccbed7) | 14's seed replay 36 min -> 8 min, 499 -> 111 MB |
| 3.3 | World depth 1 (flips of flipped runs' paths) for 05/14/31: 14's round 4 planned 12,438 obligations over 114 distinct (site, decision, arm), asked again in each of ~430 one-flip worlds, at ~24 verdicts a minute | Every study check at depth 0: flips of the seed's paths only; each of the eight bug checks' witnesses moved one root off the recording's path | `experiments/solr/solr-adhoc/case.sh` (24d3e621e) | the second generation is gone |
| 3.4 | Guards inside the system's view classes (`DocCollection`, `Slice`, `ZkNodeProps` constructors decoding `state.json`) were flipped per decode: SGF8 round 0 of 14/39/40, 615 such flips, 446 unsat, 123 replays not admitted, none admitted -- one node's decode alone never sees another value | Guards of the system's view classes are no flip sites; what else a version could hold is its writer's to state | `ClosurePlanner` (`--system-view`), `plan/SystemView#of` (solr-viewflips) | 13-73 fewer replays per round 0 |

## 4. ZooKeeper (done)

The rule (owner 2026-10-15): only the (znode, field) the causal trace puts on the anchor's chain are symbolic; for a
store path, writers and decodes are taken only up to the version the read observed.

| # | What | Code |
|---|---|---|
| 4.1 | READ doors at ZooKeeper reads (a store read's fault), doors-only control producers | solr-zk-doors (edc62b76b) |
| 4.2 | The ZooKeeper causal trace: the recording states store reads, watch events and documents' leaves; a plan row's `contentKeys` restrict a decode to the chain's fields | 9b2fa4d8c (runtime), 8ff9e1b84 (`contract.ZkChain`, GROW `ZK_EDGE`, cases), cce507fb8 (PLAN) |
| 4.3 | A finite set of fields by the trace: writers up to the version read, views at or below it, flips only on chain reads | 017939b23, `causynth/ZkCausalGraph` |
| 4.4 | ZK-carried occurrences write no heap state a target reads: a store's values cross only as the chain's leaves and views | e538a6fd5 |
| 4.5 | ZKKEYS: the seed's own composition rekeys the chain; EXPLORE flips no decision over off-chain store values alone | f8498e106 |
| 4.6 | The chain grows by its own fields only (an off-chain write or decode of a chain path's version a chain occurrence consumed, under a chain key): SGF7LOST-18413 round 2, 1099 -> 50 edges | 2a9f0f516 |
| 4.7 | A replay's store read is a row only on the chain of a planned occurrence; a replay builds no trace row | b6ec41b72 |
| 4.8 | The system's view classes add no tracked cell (`plan.SystemView`); chain writers carry the store's values through the heap | be000034c, 1d4761d4d |
| 4.9 | A keyed planned writer exports its chain fields even when doors-only (snapshot's pairing witness) | 4f4120de0 |
| 4.10 | A map's free iteration order keyed by its state's term (`assoc_view_key`): z3's theory-array incompleteness on a removal's lambda | 19416e817 |
| 4.11 | ZK fault kinds: ConnectionLoss and SessionExpired only (3.6.2 never raises OperationTimeout); a planted SessionExpired is a real expiry at the server | 2e02f345f, c5ddff24a |
| 4.12 | A view's publication is a schedule event (`PUBLISH`), held by the node's publisher; a pairing's hold (VIEW_HOLD) | STATUS "A node's view of a store path" |

## 5. Not done: the HBase refactor's list, most valuable first

| # | Problem (measured) | Design | Size, risk |
|---|---|---|---|
| 5.1 | A store-content deviation is asked at each reader (3.4 removed the view classes' guards, but any reader's guard over a store leaf is still asked per reading occurrence); realistic is the writer writing another value, which every reader sees | Ask a store leaf's alternative once per (path, field, version) at its writer: the solver's model for the leaf becomes the writer's planted write, not a reader's read | engine (explore + runtime plant), no VM change; medium |
| 5.2 | Root plants apply only on the FOCUSED occurrence (`RootMint.focusedRootValue`), so the same symbolic condition at N occurrences is N different questions; only the same (focus, model, world) is a duplicate, which the question key already catches | Key replays by the world their model plants (root, mint occurrence, value; answers; inherited flips; plan generation); a model planting a world already run or queued shares that replay's session and verdict | engine (stream dispatch, `ObligationDir`); small; exact |
| 5.3 | World depth 1 explodes (3.3); some bugs may need two deviations | Generation 2 only for conditions whose inputs the parent flip changed (the flip's root reaches the condition's term), the rest answered by the parent | explore (`ObligationFactory`, `Frontier`); medium |
| 5.4 | A heavy region is excluded by declaration (3.2), losing what it writes | Track a demanded-location occurrence's writes only on the demanded cells and their value slice (the planner names the cells per task; the runtime records only those) | PLAN + runtime + session contract; large |
| 5.5 | Narrow cases are GROW-bound: SGF8 19, rounds 2-9 a GROW cycle every 504-690 s with 0-1 obligations = GROW's planner 1.3 s + weave 63 s (cut where it repeats a tree, 1.11) + the slowest re-run 336-451 s + 21-52 s to the swap + the round's planner 65-138 s. The same 15 obligations are re-run 5-8 times (108 re-runs of 23), each re-run exposing the next store hop of the same few regions (peekElements wake #23-#37, then #59-#69, then #67, #85, ...); a re-run runs ~2x its first replay (239-269 s against 121 s, 1.0-1.1 GB against 0.25) | Batch GROW: plan, at an exposure, every occurrence of the exposed region the exposing session reached (one generation, not one per hop); plan the next round while re-runs run; swap each re-run as it returns | medium |
| 5.6 | The served planner is one JVM holding the whole corpus index (heap after 1.6: rows, expression tables, join keys, shared-body texts, memo keys holding nodes, the slot table, index keys) | Shard the index by key over hosts (map per session where it lands, reduce per key) | large; parked by the owner for Solr |
| 5.7 | SEED runs the static pass 3-4 times (initial, scope growth, demanded doors, the recording weave), 1-2 min each | Choose demanded doors in the growth pass; one pass after growth | small |
| 5.8 | The replay's session publication is engine code interpreted by the Zero VM (`RowPublication.collect`: 25 CPU minutes in 14's heavy seed); it is also each replay's memory peak | Publish rows raw and let the head decode them (a JIT JVM), or stream them during the run | medium |
| 5.9 | CONFIRM holds an activation by occurrence id, which digests a timed-wait turn's number; the native plant's ORDER rows keep `#k`: a true witness inside such a turn can wait out its timeout | Key both by the turn family, as the replay's schedule (2.1) | small |
| 5.10 | 31: the test client's polling READs (`READ /clusterstate.json#n`, n the event's k in its key) stall 16 s each | A write waiting only behind READ slots stands a grace, not the CEILING x grace deferral | small |
| 5.11 | 35 % of 14's first verdicts were NOT_ADMITTED (the focused prefix did not reproduce) | Classify by cause (schedule give-up, plant unwritten, divergence before the flip) and fix the top one | unknown |
| 5.12 | Solr-specific open: snapshot's state.json delivery race (a WIRE producer CONFIRM checks but never holds); 18413's hand WIRE_FLOW rows (the chain keys no `/overseer/queue` field) | TODO "Solr" §3y, §3aa | small each |
| 5.13 | Probe-first sibling deferral was measured and not adopted as pruning: a group's lost probe wrongly drops 5-15 % of reaching siblings even by call chain | Keep only as ordering under a budget, or not at all | -- |
| 5.14 | Several cases at once in the pool (SGF5: 13.4 h of case time in a 4 h span) | The owner's call: final rounds ran each case alone | -- |
| 5.15 | What a composed path still leaves (SGF8OOM-adhoc-14, after 1.11: ~110 MB a path over an 8.5 GB corpus, the bound at 27 of 353 paths; histogram over 3 paths: +2.4 M `LinkedHashMap` entries, +412 k `SmtLowering$Declared`, +145 MB chars): its statements, the declarations of every name its lowering touched, kept since `declared` decides root domains, pins and refutations, and its manifest rows (gaps, concrete); and the composer's old generation is 2/3 of its heap (NewRatio 2), so `Composer#HEAP_SHARE` leaves it ~1.5 GB above the corpus | Give the composer the head steps' NewRatio=4; write each path's statements and manifest rows out as it is composed (the body's declarations are reached from the statements at the end); declarations as flyweights | compose, shell (`do_compose`); medium |

## 6. For the HBase port

- Carry 1.1-1.8 and 2.1 as they are (system-agnostic); 1.5 needs the replay's life-mean measure from the start.
- Declare per system, and list in STATUS: the client's request transports (3.1), heavy region roots (3.2), the view
  classes (3.4, `system_scope`), and the coordination store's doors (HBase: ZooKeeper, its own RPC).
- Start at world depth 0 (3.3) and add 5.3 before any depth 1.
- Do 5.1 and 5.2 in the refactor: with 3.4 they remove the per-reader and duplicate-world replays.
- Tree timing workarounds (2.2): look for the same two classes (hash-ordered node sets, clock-dependent flushes)
  in the HBase tree before the first round, by reading the seed replay's give-ups (`SCHEDULE_DIVERGED` rows).
- Measure before claiming a speed-up (two flag fixes of 2026-10-16 failed: the overhead limit's eden condition);
  every number above came from a run or an offline A/B with identical outputs.
